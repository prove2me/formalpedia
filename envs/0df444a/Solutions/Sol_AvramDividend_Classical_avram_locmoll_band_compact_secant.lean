-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_compact_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:26:36.354016+00:00
-- url     : https://prove2.me/submissions/e1278429-2b33-4c4c-9d51-52ff785ddff9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a ∈ Icc 0 R, ∀ b ∈ Icc 0 R,
      |g a - g b| ≤ K * |a - b| := by 
  have hcont : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  obtain ⟨K, hK⟩ := (isCompact_Icc.image hcont.norm).bddAbove
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro a ha b hb
  have hbound : ∀ z ∈ Icc (0 : ℝ) R, ‖deriv g z‖ ≤ max K 0 :=
    fun z hz => (hK ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0 : ℝ) R).norm_image_sub_le_of_norm_deriv_le (fun z _ => hd z) hbound hb ha
