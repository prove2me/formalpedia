-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_finitecap_beta22_kink_signed_quadratic_variation_correction_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:04:23.877343+00:00
-- url     : https://prove2.me/submissions/82f21224-1bac-4d69-b11c-77683c20c587

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_beta22_one_sided_hinge_nonnegative_curvature_off_transition_levels
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (σ α b ε y : ℝ) (hε : 0 < ε) (hα : 1 ≤ α)
    (hb : y ≠ b) (hu : y ≠ b + ε) :
    (σ ^ 2 / 2) * (1 - α) *
      iteratedDeriv 2 (fun z : ℝ => if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2) y ≤ 0 := by
  have hcurv :=
    avram_ga_beta22_one_sided_hinge_nonnegative_curvature_off_transition_levels
      b ε y hε hb hu
  have hσ : 0 ≤ σ ^ 2 / 2 :=
    div_nonneg (sq_nonneg σ) (by norm_num)
  have hα' : 1 - α ≤ 0 := by linarith
  have hneg : (σ ^ 2 / 2) * (1 - α) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hσ hα'
  exact mul_nonpos_of_nonpos_of_nonneg hneg hcurv
