use std::iter;
use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector, VirtualCells},
    circuit::{self, AssignedCell, Layouter, Region},
    poly::Rotation,
};

use crate::{
    hash_type::HashType,
    matrix,
    mds::generate_mds,
    poseidon::{Arity, PoseidonConstants},
};

const ALPHA: u64 = 5;

#[derive(Clone, Debug)]
pub struct PoseidonConfig<F, A>
where
    F: FieldExt,
    A: Arity<F>,
{
    state: Vec<Column<Advice>>,
    partial_sbox: Column<Advice>,
    rc_a: Vec<Column<Fixed>>,
    rc_b: Vec<Column<Fixed>>,
    s_full: Selector,
    s_partial: Selector,
    _f: PhantomData<F>,
    _a: PhantomData<A>,
}

pub struct PoseidonChip<F, A>
where
    F: FieldExt,
    A: Arity<F>,
{
    config: PoseidonConfig<F, A>,
}

impl<F, A> PoseidonChip<F, A>
where
    F: FieldExt,
    A: Arity<F>,
{
    pub fn construct(config: PoseidonConfig<F, A>) -> Self {
        PoseidonChip { config }
    }

    // # Side Effects
    //
    // - All `io` columns will be equality constrained.
    // - The first `fixed` column will be equality constrained.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        io: Vec<Column<Advice>>,
        extra: Column<Advice>,
        fixed: Vec<Column<Fixed>>,
    ) -> PoseidonConfig<F, A> {
        let width = A::to_usize() + 1;

        assert_eq!(io.len(), width);
        assert_eq!(fixed.len(), 2 * width);

        // Rename columns.
        let state = io;
        let partial_sbox = extra;
        let rc_b = fixed[..width].to_vec();
        let rc_a = fixed[width..].to_vec();

        // Allows the preimage to be copied into the hash function's region.
        for col in state.iter() {
            meta.enable_equality(*col);
        }
        // Allows the domain tag to be copied into the first state column.
        meta.enable_constant(rc_b[0]);

        let s_full = meta.selector();
        let s_partial = meta.selector();

        let mds = generate_mds::<F>(width);
        let mds_inv = matrix::invert(&mds).expect("mds matrix in non-invertible");

        let pow_5 = |v: Expression<F>| {
            let v2 = v.clone() * v.clone();
            v2.clone() * v2 * v
        };

        meta.create_gate("full round", |meta| {
            let s_full = meta.query_selector(s_full);

            // Assert that the dot product of the current round's (i.e. rows's) state with the MDS
            // matrix is equal to the next round's state.
            (0..width)
                .map(|i| {
                    let next_elem = meta.query_advice(state[i], Rotation::next());
                    let dot_prod = (0..width)
                        .map(|j| {
                            let elem = meta.query_advice(state[j], Rotation::cur());
                            let c = meta.query_fixed(rc_a[j], Rotation::cur());
                            pow_5(elem + c) * mds[j][i]
                        })
                        .reduce(|dot_prod, next| dot_prod + next)
                        .unwrap();
                    s_full.clone() * (dot_prod - next_elem)
                })
                .collect::<Vec<_>>()
        });

        // Perform two partial rounds (A and B).
        meta.create_gate("partial rounds", |meta| {
            let s_partial = meta.query_selector(s_partial);

            // The first element of round A's input state
            let a_in_0 = meta.query_advice(state[0], Rotation::cur());
            let a_sbox_out_0 = meta.query_advice(partial_sbox, Rotation::cur());

            // Compute the `i`-th state element output by round A (equivalent to round B's `i`-th
            // input state element.
            let a_out = |i: usize, meta: &mut VirtualCells<F>| {
                let dot_prod = a_sbox_out_0.clone() * mds[i][0];
                (1..width).fold(dot_prod, |dot_prod, j| {
                    let a_in_j = meta.query_advice(state[j], Rotation::cur());
                    let c = meta.query_fixed(rc_a[j], Rotation::cur());
                    dot_prod + (a_in_j + c) * mds[i][j]
                })
            };

            // Compute the `i`-th sbox output for round B by computing the dot product of B's output
            // state with the `i`-th column of the inverse MDS matrix.
            let b_sbox_out = |i: usize, meta: &mut VirtualCells<F>| {
                (0..width)
                    .map(|j| {
                        let b_out_j = meta.query_advice(state[j], Rotation::next());
                        b_out_j * mds_inv[i][j]
                    })
                    .reduce(|dot_prod, next| dot_prod + next)
                    .unwrap()
            };

            // Apply the sbox to the first elemet of round A's input state and assert that it is
            // equal to the value in the `partial_sbox` column of the current row.
            let a_sbox_out_0 = {
                let c = meta.query_fixed(rc_a[0], Rotation::cur());
                s_partial.clone() * (pow_5(a_in_0 + c) - a_sbox_out_0.clone())
            };

            // Compute the first state element output by round A (i.e. B's first input state
            // element) and assert that it is equal to the dot product of round B's output state and
            // the first column of the inverse MDS matrix.
            let b_sbox_out_0 = {
                let b_in_0 = a_out(0, meta);
                let c = meta.query_fixed(rc_b[0], Rotation::cur());
                s_partial.clone() * (pow_5(b_in_0 + c) - b_sbox_out(0, meta))
            };

            // For each element `i > 0`, compute the `i`-th input state element for round B and
            // assert that its sum, with the corresponding round constant, is equal to round B's
            // `i`-th output state element (computed by taking the dot product of B's output state
            // with the `i`-th column of the inverse MDS matrix).
            let b_out_linear = (1..width).map(|i| {
                let b_in_i = a_out(i, meta);
                let c = meta.query_fixed(rc_b[i], Rotation::cur());
                s_partial.clone() * (b_in_i + c - b_sbox_out(i, meta))
            });

            iter::once(a_sbox_out_0)
                .chain(iter::once(b_sbox_out_0))
                .chain(b_out_linear)
                .collect::<Vec<_>>()
        });

        PoseidonConfig {
            state,
            partial_sbox,
            rc_a,
            rc_b,
            s_full,
            s_partial,
            _f: PhantomData,
            _a: PhantomData,
        }
    }

    // Assign the initial state `domain tag || preimage` into the state vector of the provided row.
    fn assign_initial_state(
        &self,
        region: &mut Region<F>,
        consts: &PoseidonConstants<F, A>,
        preimage: &[AssignedCell<F, F>],
        row: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let width = A::to_usize() + 1;

        let mut state = Vec::<AssignedCell<F, F>>::with_capacity(width);

        // Assign the domain tag into a fixed column and copy the assigned value into the
        // first initial state element.
        let domain_tag = region.assign_advice_from_constant(
            || "domain tag",
            self.config.state[0],
            row,
            consts.domain_tag,
        )?;
        state.push(domain_tag);

        // Copy the preimage into the remaining initial state elements.
        for (i, elem) in preimage.iter().enumerate() {
            state.push(elem.copy_advice(
                || format!("initial state {} (preimage {})", i + 1, i),
                region,
                self.config.state[i + 1],
                row,
            )?);
        }

        Ok(state)
    }

    fn assign_round_constants(
        &self,
        region: &mut Region<F>,
        consts: &PoseidonConstants<F, A>,
        cols: &[Column<Fixed>],
        round: usize,
        row: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let width = A::to_usize() + 1;
        consts
            .round_constants
            .iter()
            .skip(round * width)
            .take(width)
            .zip(cols.iter())
            .enumerate()
            .map(|(i, (c, col))| {
                region.assign_fixed(
                    || format!("round constant {} (round {})", i, round),
                    *col,
                    row,
                    || circuit::Value::known(*c),
                )
            })
            .collect()
    }

    fn assign_state(
        &self,
        region: &mut Region<F>,
        state: &[circuit::Value<F>],
        round: usize,
        row: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        state
            .iter()
            .zip(self.config.state.iter())
            .enumerate()
            .map(|(i, (word, col))| {
                region.assign_advice(
                    || format!("state {} (round {})", i, round),
                    *col,
                    row,
                    || *word,
                )
            })
            .collect()
    }

    // Perform a full round on `state` and assign the output state in the next row.
    fn full_round(
        &self,
        region: &mut Region<F>,
        consts: &PoseidonConstants<F, A>,
        state: &[AssignedCell<F, F>],
        round: usize,
        row: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let width = A::to_usize() + 1;

        self.config.s_full.enable(region, row)?;
        self.assign_round_constants(region, consts, &self.config.rc_a, round, row)?;

        let round_consts = consts
            .round_constants
            .iter()
            .skip(round * width)
            .take(width);

        let mds = &consts.mds_matrices.m;
        let mds_cols = (0..width).map(|col| (0..width).map(move |row| mds[row][col]));

        // Add a round constant to each state elememt, then apply the sbox to each sum.
        let sbox_out: Vec<circuit::Value<F>> = state
            .iter()
            .zip(round_consts)
            .map(|(word, rc)| word.value().map(|word| (*word + rc).pow_vartime([ALPHA])))
            .collect();

        let next_state: Vec<circuit::Value<F>> = mds_cols
            .map(|mds_col| {
                let mut dot_prod = circuit::Value::known(F::zero());
                for (sbox_out, m) in sbox_out.iter().zip(mds_col) {
                    let sbox_out_times_m = sbox_out.map(|sbox_out| sbox_out * m);
                    dot_prod = dot_prod + sbox_out_times_m;
                }
                dot_prod
            })
            .collect();

        self.assign_state(region, &next_state, round + 1, row + 1)
    }

    // Perform 2 partial rounds (A and B) on `state` and assign the output state in the next row.
    fn partial_rounds(
        &self,
        region: &mut Region<F>,
        consts: &PoseidonConstants<F, A>,
        state: &[AssignedCell<F, F>],
        round: usize,
        row: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let width = A::to_usize() + 1;

        let round_a = round;
        let round_b = round + 1;

        self.config.s_partial.enable(region, row)?;

        // Assign the first and second rounds' round constants in the `rc_a` and `rc_b` columns
        // respectively.
        self.assign_round_constants(region, consts, &self.config.rc_a, round_a, row)?;
        self.assign_round_constants(region, consts, &self.config.rc_b, round_b, row)?;

        let round_consts_a = consts
            .round_constants
            .iter()
            .skip(round_a * width)
            .take(width);

        let round_consts_b = consts
            .round_constants
            .iter()
            .skip(round_b * width)
            .take(width);

        let mds = &consts.mds_matrices.m;
        let mds_cols = (0..width).map(|col| (0..width).map(move |row| mds[row][col]));

        // Add a round constant to each state elememt, then apply the sbox to the first sum.
        let sbox_out_a: Vec<circuit::Value<F>> = state
            .iter()
            .zip(round_consts_a)
            .enumerate()
            .map(|(i, (word, rc))| {
                if i == 0 {
                    word.value().map(|word| (*word + rc).pow_vartime([ALPHA]))
                } else {
                    word.value().map(|word| *word + rc)
                }
            })
            .collect();

        // Assign the first state element's sbox output in the `partial_sbox` column.
        region.assign_advice(
            || format!("partial sbox output (round {})", round_a),
            self.config.partial_sbox,
            row,
            || sbox_out_a[0],
        )?;

        let input_state_b: Vec<circuit::Value<F>> = mds_cols
            .map(|mds_col| {
                let mut dot_prod = circuit::Value::known(F::zero());
                for (sbox_out, m) in sbox_out_a.iter().zip(mds_col) {
                    let sbox_out_times_m = sbox_out.map(|sbox_out| sbox_out * m);
                    dot_prod = dot_prod + sbox_out_times_m;
                }
                dot_prod
            })
            .collect();

        // Add the associated round constant to each state elememt, then apply the sbox to the first
        // element.
        let sbox_out_b: Vec<circuit::Value<F>> = input_state_b
            .iter()
            .zip(round_consts_b)
            .enumerate()
            .map(|(i, (word, rc))| {
                if i == 0 {
                    word.as_ref().map(|word| (*word + rc).pow_vartime([ALPHA]))
                } else {
                    word.as_ref().map(|word| *word + rc)
                }
            })
            .collect();

        let mds_cols = (0..width).map(|col| (0..width).map(move |row| mds[row][col]));

        // Multiply the sbox outputs by the MDS matrix.
        let output_state_b: Vec<circuit::Value<F>> = mds_cols
            .map(|mds_col| {
                let mut dot_prod = circuit::Value::known(F::zero());
                for (sbox_out, m) in sbox_out_b.iter().zip(mds_col) {
                    let sbox_out_times_m = sbox_out.map(|sbox_out| sbox_out * m);
                    dot_prod = dot_prod + sbox_out_times_m;
                }
                dot_prod
            })
            .collect();

        self.assign_state(region, &output_state_b, round_b + 1, row + 1)
    }

    pub fn hash(
        &self,
        mut layouter: impl Layouter<F>,
        preimage: &[AssignedCell<F, F>],
        consts: &PoseidonConstants<F, A>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let arity = A::to_usize();
        let width = arity + 1;

        assert!(arity > 0);
        assert_eq!(preimage.len(), arity);

        // This circuit does not support padding the preimage with zeros, i.e. if the hash-type is
        // `ConstantLength`, the constant length must be equal to the width.
        assert!(consts.hash_type.is_supported());
        if let HashType::ConstantLength(const_len) = consts.hash_type {
            assert_eq!(const_len, width);
        };

        // This gadget requires that both the number of full and partial rounds are even.
        assert_eq!(consts.full_rounds & 1, 0);
        assert_eq!(consts.partial_rounds & 1, 0);

        layouter.assign_region(
            || "poseidon",
            |mut region| {
                let mut round = 0;
                let mut row = 0;

                let mut state = self.assign_initial_state(&mut region, consts, preimage, row)?;

                for _ in 0..consts.half_full_rounds {
                    state = self.full_round(&mut region, consts, &state, round, row)?;
                    round += 1;
                    row += 1;
                }

                for _ in 0..consts.partial_rounds / 2 {
                    state = self.partial_rounds(&mut region, consts, &state, round, row)?;
                    round += 2;
                    row += 1;
                }

                for _ in 0..consts.half_full_rounds {
                    state = self.full_round(&mut region, consts, &state, round, row)?;
                    round += 1;
                    row += 1;
                }

                Ok(state[1].clone())
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use generic_array::typenum::{Unsigned, U11, U2, U4, U8};
    use halo2_proofs::{
        arithmetic::{CurveAffine, CurveExt, FieldExt},
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        pasta::{EqAffine, Fp, Fq},
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, Error, Instance,
            SingleVerifier,
        },
        poly::commitment::Params,
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    };
    use rand::rngs::OsRng;

    use crate::{round_numbers::round_numbers_halo, Poseidon, Strength};

    #[test]
    fn test_poseidon_chip() {
        #[derive(Clone)]
        struct MyConfig<F, A>
        where
            F: FieldExt,
            A: Arity<F>,
        {
            poseidon: PoseidonConfig<F, A>,
            // Instance column to pass in expected digest.
            pi_col: Column<Instance>,
        }

        struct MyCircuit<F, A>
        where
            F: FieldExt,
            A: Arity<F>,
        {
            preimage: Vec<circuit::Value<F>>,
            _a: PhantomData<A>,
        }

        impl<F, A> Circuit<F> for MyCircuit<F, A>
        where
            F: FieldExt,
            A: Arity<F>,
        {
            type Config = MyConfig<F, A>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                MyCircuit {
                    preimage: vec![circuit::Value::unknown(); self.preimage.len()],
                    _a: PhantomData,
                }
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let width = A::to_usize() + 1;

                let io = (0..width).map(|_| meta.advice_column()).collect();
                let extra = meta.advice_column();
                let fixed = (0..2 * width).map(|_| meta.fixed_column()).collect();
                let poseidon = PoseidonChip::<F, A>::configure(meta, io, extra, fixed);

                let pi_col = meta.instance_column();
                meta.enable_equality(pi_col);

                MyConfig { poseidon, pi_col }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                // The digest public input is stored in the first absolute row.
                const PI_ROW: usize = 0;

                let MyConfig {
                    poseidon: poseidon_config,
                    pi_col,
                } = config;

                let preimage: Vec<AssignedCell<F, F>> = layouter.assign_region(
                    || "preimage",
                    |mut region| {
                        let offset = 0;
                        self.preimage
                            .iter()
                            .zip(poseidon_config.state.iter())
                            .enumerate()
                            .map(|(i, (word, col))| {
                                region.assign_advice(
                                    || format!("preimage elem {}", i),
                                    *col,
                                    offset,
                                    || *word,
                                )
                            })
                            .collect()
                    },
                )?;

                let hasher_chip = PoseidonChip::<F, A>::construct(poseidon_config);
                let consts = PoseidonConstants::<F, A>::new_with_strength(Strength::Halo);
                let digest =
                    hasher_chip.hash(layouter.namespace(|| "poseidon"), &preimage, &consts)?;

                layouter.constrain_instance(digest.cell(), pi_col, PI_ROW)?;

                Ok(())
            }
        }

        impl<F, A> MyCircuit<F, A>
        where
            F: FieldExt,
            A: Arity<F>,
        {
            fn with_witness(preimage: &[F]) -> Self {
                assert_eq!(preimage.len(), A::to_usize());
                MyCircuit {
                    preimage: preimage.iter().map(|word| circuit::Value::known(*word)).collect(),
                    _a: PhantomData,
                }
            }

            fn generate_public_inputs(digest: F) -> Vec<Vec<F>> {
                vec![vec![digest]]
            }

            // `k = ceil(log2(num_circuit_rows))`
            fn k() -> u32 {
                let arity = A::to_usize();
                let (rf, rp) = round_numbers_halo(arity);
                let poseidon_rows = rf + rp / 2;
                // Add one row for preimage allocation.
                let num_rows = (poseidon_rows + 1) as f32;
                num_rows.log2().ceil() as u32
            }
        }

        fn test_poseidon_chip_inner<F, A>()
        where
            F: FieldExt,
            A: Arity<F>,
        {
            let arity = A::to_usize();
            let preimage: Vec<F> = (0..arity).map(|i| F::from(i as u64)).collect();
            let consts = PoseidonConstants::<F, A>::new_with_strength(Strength::Halo);
            let digest = Poseidon::new_with_preimage(&preimage, &consts).hash();
            let circ = MyCircuit::<F, A>::with_witness(&preimage);
            let pub_inputs = MyCircuit::<F, A>::generate_public_inputs(digest);
            let k = MyCircuit::<F, A>::k();
            let prover = MockProver::run(k, &circ, pub_inputs).unwrap();
            assert!(prover.verify().is_ok());
        }

        test_poseidon_chip_inner::<Fp, U2>();
        test_poseidon_chip_inner::<Fp, U4>();
        test_poseidon_chip_inner::<Fp, U8>();
        test_poseidon_chip_inner::<Fp, U11>();
    }

    #[test]
    fn test_poseidon_chip_prove_verify() {
        #[derive(Clone)]
        struct MyConfig {
            poseidon: PoseidonConfig<Fp, U2>,
            advice: [Column<Advice>; 2],
        }

        struct MyCircuit {
            preimage: [circuit::Value<Fp>; 2],
        }

        impl Circuit<Fp> for MyCircuit {
            type Config = MyConfig;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                MyCircuit {
                    preimage: [circuit::Value::unknown(); 2],
                }
            }

            fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
                let width = 3;
                let state: Vec<Column<Advice>> = (0..width).map(|_| meta.advice_column()).collect();
                let advice = [state[0], state[1]];
                let extra = meta.advice_column();
                let fixed = (0..2 * width).map(|_| meta.fixed_column()).collect();
                let poseidon = PoseidonChip::<Fp, U2>::configure(meta, state, extra, fixed);
                MyConfig { poseidon, advice }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<Fp>,
            ) -> Result<(), Error> {
                let MyConfig {
                    poseidon: poseidon_config,
                    advice,
                } = config;

                let poseidon_chip = PoseidonChip::construct(poseidon_config);

                let preimage = layouter.assign_region(
                    || "assign preimage",
                    |mut region| {
                        let offset = 0;
                        let elem_1 = region.assign_advice(
                            || "preimage elem 1",
                            advice[0],
                            offset,
                            || self.preimage[0],
                        )?;
                        let elem_2 = region.assign_advice(
                            || "preimage elem 2",
                            advice[1],
                            offset,
                            || self.preimage[1],
                        )?;
                        Ok(vec![elem_1, elem_2])
                    },
                )?;

                let _digest = poseidon_chip.hash(
                    layouter.namespace(|| "poseidon"),
                    &preimage,
                    &PoseidonConstants::<Fp, U2>::new_with_strength(Strength::Halo),
                )?;

                Ok(())
            }
        }

        let circ = MyCircuit {
            preimage: [
                circuit::Value::known(Fp::one()),
                circuit::Value::known(Fp::zero() - Fp::one())
            ],
        };

        // `k = ceil(log2(r_f + r_p / 2))`
        let k = 6;

        let prover = MockProver::run(k, &circ, vec![]).unwrap();
        assert!(prover.verify().is_ok());

        let params = Params::<EqAffine>::new(k);
        let pk = {
            let vk = keygen_vk(&params, &circ).expect("failed to create verifying key");
            keygen_pk(&params, vk, &circ).expect("failed to create proving key")
        };
        let vk = pk.get_vk();

        type TranscriptReader<'proof> = Blake2bRead<&'proof [u8], EqAffine, Challenge255<EqAffine>>;
        type TranscriptWriter = Blake2bWrite<Vec<u8>, EqAffine, Challenge255<EqAffine>>;

        let mut transcript = TranscriptWriter::init(vec![]);
        create_proof(&params, &pk, &[circ], &[&[]], &mut OsRng, &mut transcript)
            .expect("failed to create halo2 proof");
        let proof_bytes: Vec<u8> = transcript.finalize();

        let mut transcript = TranscriptReader::init(&proof_bytes);
        let verifier_strategy = SingleVerifier::new(&params);
        verify_proof(&params, vk, verifier_strategy, &[&[]], &mut transcript)
            .expect("failed to verify halo2 proof");
    }
}
