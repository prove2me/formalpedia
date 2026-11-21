-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_beta22_one_sided_hinge_nonnegative_curvature_off_transition_levels
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:37:22.455175+00:00
-- url     : https://prove2.me/submissions/15d0ba39-89c4-47cd-a240-1cb00629e4ad

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ga_finitecap_explicit_one_sided_beta22_mollified_hinge_interior_curvature
import Theorems.Thm_AvramDividend_Classical_avram_ga_beta22_one_sided_hinge_curvature_zero_off_smoothing_strip
open Set Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (b ε y : ℝ) (hε : 0 < ε) (hb : y ≠ b) (hu : y ≠ b + ε) :
    let Q : ℝ → ℝ := fun z : ℝ => if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2
    0 ≤ iteratedDeriv 2 Q y := by
  change 0 ≤ iteratedDeriv 2
    (fun z : ℝ => if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2) y
  by_cases hlo : y < b
  · rw [avram_ga_beta22_one_sided_hinge_curvature_zero_off_smoothing_strip
      b ε y hε (Or.inl hlo)]
  by_cases hhi : b + ε < y
  · rw [avram_ga_beta22_one_sided_hinge_curvature_zero_off_smoothing_strip
      b ε y hε (Or.inr hhi)]
  have hby : b < y :=
    lt_of_le_of_ne (le_of_not_gt hlo) (Ne.symm hb)
  have hyu : y < b + ε :=
    lt_of_le_of_ne (le_of_not_gt hhi) hu
  exact (avram_ga_finitecap_explicit_one_sided_beta22_mollified_hinge_interior_curvature
    b ε y hε hby hyu).2.2
