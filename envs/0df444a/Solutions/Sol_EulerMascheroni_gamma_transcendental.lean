-- Prove2me | solution 1 for EulerMascheroni.gamma_transcendental
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T12:50:57.209622+00:00
-- url     : https://prove2.me/submissions/16102ce3-f96c-4c54-a193-b531abf6f59f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EulerMascheroni_Mixed_hardy_identity
import Theorems.Thm_EulerMascheroni_Mixed_value_relation_lifting_conjecture
import Theorems.Thm_EulerMascheroni_Mixed_kernel_coefficient_vanishes

open EulerMascheroni.Mixed

/-- A conditional reduction: the arithmetic lifting child remains conjectural. -/
theorem solution : Transcendental ℚ Real.eulerMascheroniConstant := by
  intro hγ
  have hrel : (0 : ℂ) + ((-Real.eulerMascheroniConstant : ℝ) : ℂ) * Complex.exp 1 +
      (1 : ℂ) * expEin 1 + (-1 : ℂ) * kernelOnCover 0 = 0 := by
    simp only [expEin, kernelOnCover, Complex.exp_zero, sub_self, sub_zero,
      one_mul, neg_one_mul, zero_add, Complex.ofReal_neg]
    rw [hardy_identity]
    ring
  obtain ⟨P, Q, R, S, _, _, _, hS, hfunctional⟩ :=
    value_relation_lifting_conjecture 0 (-Real.eulerMascheroniConstant) 1 (-1)
      isAlgebraic_zero hγ.neg isAlgebraic_one isAlgebraic_one.neg (by simpa using hrel)
  have hzero := kernel_coefficient_vanishes P Q R S hfunctional
  rw [hS] at hzero
  norm_num at hzero
