-- Prove2me | solution 1 for BookProof.ChapterA3.adj2_mul_T
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:36:02.290957+00:00
-- url     : https://prove2.me/submissions/992ceb41-8971-49cc-8dae-877d778ffb76

-- Generated from ChapterA3i.lean — solution of BookProof.ChapterA3.adj2_mul_T
import Mathlib
import Definitions.Def_ChapterA3i
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) :
    adj2 T * T = 1 := by

  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [adj2, Fin.isValue, Fin.zero_eta, mul_apply, of_apply, cons_val', cons_val_fin_one,
        cons_val_zero, Fin.sum_univ_two, cons_val_one, neg_mul, one_apply_eq, Fin.mk_one, ne_eq,
            zero_ne_one, not_false_eq_true, one_apply_ne, one_ne_zero] <;>
    first | linear_combination hdet | ring
