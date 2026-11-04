-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_canonical_candidate_nonnegative_at_or_below_ENNReal_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:01:47.879421+00:00
-- url     : https://prove2.me/submissions/fdfcc53b-0c9e-4e38-a28d-b5ca382cd29b

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_interior_nonnegative_gradient_preserves_boundary_payoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact canonical interior gradient and boundary condition force w≥0
    at every reserve below the ENNReal cap, including its finite endpoint. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (y : ℝ) (hyC : ENNReal.ofReal y ≤ C) :
    0 ≤ w y := by
  by_cases hyneg : y < 0
  · simp [hw_neg y hyneg]
  have hy : 0 ≤ y := le_of_not_gt hyneg
  have hcont : ContinuousOn w (Icc 0 y) := by
    apply hw_cont.mono
    intro z hz
    exact hz.1
  have hsub : Ioo 0 y ⊆ {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hzY : ENNReal.ofReal z < ENNReal.ofReal y :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hz.1)).mpr hz.2
    exact lt_of_lt_of_le hzY hyC
  have hdiff : DifferentiableOn ℝ w (Ioo 0 y) :=
    (hw_smooth.differentiableOn (by norm_num)).mono hsub
  have hgrad : ∀ z ∈ Ioo 0 y, 0 ≤ deriv w z := by
    intro z hz
    have hzC : ENNReal.ofReal z < C := (hsub hz).2
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (hw_grad z hz.1 hzC)
  exact avram_p4_e_localise_interior_nonnegative_gradient_preserves_boundary_payoff
    w y hy hw0 hcont hdiff hgrad
