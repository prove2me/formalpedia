-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_infinite_cap_candidate_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:13:45.987991+00:00
-- url     : https://prove2.me/submissions/dcc143a9-1869-414a-8385-6088ee33d237

import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_infinite_cap_candidate_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original C=∞ HJB candidate is globally monotone, including its
    zero extension across negative reserves and its boundary at zero. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hCtop : C = ⊤)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    Monotone w := by
  have hinside : interior (Ici (0 : ℝ)) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    have hpos : 0 < y := by simpa using hy
    exact ⟨hpos, by simp [hCtop]⟩
  have hdiff : DifferentiableOn ℝ w (interior (Ici (0 : ℝ))) :=
    (hw_smooth.differentiableOn (by norm_num)).mono hinside
  have hgrad : ∀ y ∈ interior (Ici (0 : ℝ)), 0 ≤ deriv w y := by
    intro y hy
    have hi := hinside hy
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (hw_grad y hi.1 hi.2)
  have hmono : MonotoneOn w (Ici (0 : ℝ)) :=
    monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hw_cont hdiff hgrad
  intro a b hab
  by_cases hbneg : b < 0
  · have haneg : a < 0 := lt_of_le_of_lt hab hbneg
    simp [hw_neg a haneg, hw_neg b hbneg]
  by_cases haneg : a < 0
  · rw [hw_neg a haneg]
    exact avram_p4_f_assembly_original_infinite_cap_candidate_nonnegative
      w C hCtop hw0 hw_cont hw_neg hw_smooth hw_grad b
  · exact hmono (le_of_not_gt haneg) (le_of_not_gt hbneg) hab