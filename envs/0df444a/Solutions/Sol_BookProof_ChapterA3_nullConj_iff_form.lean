-- Prove2me | solution 1 for BookProof.ChapterA3.nullConj_iff_form
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:52:42.378988+00:00
-- url     : https://prove2.me/submissions/6ba50507-0bd3-4960-a612-9846ba727ffe

-- Generated from ChapterA4d.lean — solution of BookProof.ChapterA3.nullConj_iff_form
import Mathlib
import Definitions.Def_ChapterA4d
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) :
    Tᴴ * (pauliσ 0 + pauliσ 3) * T = pauliσ 0 + pauliσ 3 ↔
      T 0 1 = 0 ∧ Complex.normSq (T 0 0) = 1 := by

  constructor <;> intro h
  · simp_all [← Matrix.ext_iff, Fin.forall_fin_two, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.normSq]
    simp_all [Complex.ext_iff, pauliσ]
    linarith
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp_all only [Fin.isValue, Fin.zero_eta, mul_apply, conjTranspose_apply, RCLike.star_def,
          Matrix.add_apply, Fin.sum_univ_succ, Finset.univ_unique, Fin.default_eq_zero,
              Finset.sum_singleton, Fin.succ_zero_eq_one, Fin.mk_one, mul_zero, zero_add, map_zero,
                  zero_mul] <;> ring
    · simp_all [Complex.ext_iff, pauliσ]
      norm_num [Complex.normSq] at h; constructor <;> linarith
    · simp_all [pauliσ]
    · simp_all [pauliσ]
    · unfold pauliσ; norm_num
