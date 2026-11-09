-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat25_topcap_candidate_nonnegative_global
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T16:35:18.682019+00:00
-- url     : https://prove2.me/submissions/d396f9b4-4561-4e65-8ba4-5df6d2ccd076

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal NNReal
noncomputable section

/-- The strictly increasing C1 candidate is nonnegative at every reserve when C is infinite. -/
theorem solution
    (C : ℝ≥0∞) (hTop : C = ⊤) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ w y := by
  intro y
  by_cases hy : y < 0
  · rw [hw_neg y hy]
  · have hy0 : 0 ≤ y := le_of_not_gt hy
    have hC : 0 < C := by simp [hTop]
    have hyC : ENNReal.ofReal y < C := by simp [hTop]
    have hBound :=
      AvramDividend.Classical.avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
        C hC w hw_cont hw0 hw_smooth hw_grad y hy0 hyC
    exact hBound y (Set.mem_Icc.mpr ⟨hy0, le_rfl⟩)
