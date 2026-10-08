-- Prove2me | solution 1 for AvramDividend.Classical.cstar_zero_barrier_compare_of_no_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T15:31:06.180396+00:00
-- url     : https://prove2.me/submissions/cd059b33-47dd-4f03-be2d-9116b624e344

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_optimal_barrier_of_shape

open AvramDividend.Classical
open scoped ENNReal

theorem solution (W : ℝ → ℝ)
    (hnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y)
    (hno : ¬(cstarSet W).Nonempty)
    (hderiv0 : ∀ x : ℝ, 0 < x →
      derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal))
    (hW0 : W 0 = 0) :
    cstar W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ a →
        barrierValue W a x ≤ vcstar W x := by
  have hc : cstar W = (0 : ℝ≥0∞) := by
    unfold cstar
    rw [if_neg hno, if_pos hderiv0]
  have hf : cstar W < ⊤ := by
    simp [hc]
  apply cstar_optimal_barrier_of_shape W hf hnonneg
  left
  exact ⟨by simp [hc], hW0⟩
