-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_infinite_cap_candidate_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:37:09.999488+00:00
-- url     : https://prove2.me/submissions/2ce8f297-fb12-4cde-bc35-a8b433fca1ca

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_interior_nonnegative_gradient_preserves_boundary_payoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Under the canonical unbounded cap, the original interior gradient
    and the actual zero extension force w nonnegative on all reserves. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hCtop : C = ⊤)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ w y := by
  intro y
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
    rw [hCtop]
    exact ENNReal.ofReal_lt_top
  have hdiff : DifferentiableOn ℝ w (Ioo 0 y) :=
    (hw_smooth.differentiableOn (by norm_num)).mono hsub
  have hgrad : ∀ z ∈ Ioo 0 y, 0 ≤ deriv w z := by
    intro z hz
    have hzC : ENNReal.ofReal z < C := hsub hz |>.2
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (hw_grad z hz.1 hzC)
  exact avram_p4_e_localise_interior_nonnegative_gradient_preserves_boundary_payoff
    w y hy hw0 hcont hdiff hgrad
