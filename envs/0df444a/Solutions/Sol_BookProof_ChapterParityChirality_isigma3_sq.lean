-- Prove2me | solution 1 for BookProof.ChapterParityChirality.isigma3_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:40.265575+00:00
-- url     : https://prove2.me/submissions/f1d3a623-2803-4584-8c98-6a755d87288c

-- Generated from ChapterParityChirality.lean — solution of BookProof.ChapterParityChirality.isigma3_sq
import Mathlib
import Definitions.Def_ChapterParityChirality
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParitySU2
open BookProof.ChapterParityChirality



open Matrix
open scoped Kronecker


open BookProof.ChapterA3
open BookProof.ChapterParity
open BookProof.ChapterParitySU2

set_option maxHeartbeats 1000000 in
theorem solution : isigma3 * isigma3 = -1 := by

  ext ⟨ i, j ⟩ ⟨ k, l ⟩ ; norm_num [ isigma3 ];
  fin_cases i <;> fin_cases k <;> simp only [kroneckerMap, Matrix.smul_apply, smul_eq_mul,
      Fin.zero_eta,
      Fin.isValue, mul_apply, of_apply, Fin.mk_one, ne_eq, Prod.mk.injEq, zero_ne_one, false_and,
          not_false_eq_true, one_apply_ne, neg_zero, one_ne_zero];
  · fin_cases j <;> fin_cases l <;> simp only [Fin.isValue, one_apply, Fin.zero_eta, mul_ite,
      mul_one, mul_zero, ite_mul, zero_mul, Fin.mk_one, Prod.mk.injEq, zero_ne_one, and_false,
          Fin.reduceFinMk, Fin.reduceEq, one_ne_zero];
    all_goals erw [ Finset.sum_product ] ; simp [ Fin.sum_univ_succ, pauli3 ] ;
  · fin_cases j <;> fin_cases l <;> simp only [pauli3, Fin.isValue, of_apply, cons_val',
      cons_val_fin_one, cons_val_zero, cons_val_one];
    all_goals erw [ Finset.sum_product ] ; simp [ Fin.sum_univ_succ, Matrix.one_apply ] ;
  · fin_cases j <;> fin_cases l <;> simp only [pauli3, Fin.isValue, of_apply, cons_val',
      cons_val_fin_one, cons_val_one, cons_val_zero];
    all_goals erw [ Finset.sum_product ] ; simp [ Fin.sum_univ_succ, Matrix.one_apply ] ;
  · fin_cases j <;> fin_cases l <;> simp only [pauli3, Fin.isValue, of_apply, cons_val',
      cons_val_fin_one, cons_val_one, one_apply, Fin.zero_eta, mul_ite, mul_one, mul_zero, ite_mul,
          zero_mul, Fin.mk_one, Prod.mk.injEq, zero_ne_one, and_false, Fin.reduceFinMk,
              Fin.reduceEq, one_ne_zero];
    all_goals erw [ Finset.sum_product ] ; simp [ Fin.sum_univ_succ ] ;
