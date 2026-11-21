-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_finitecap_explicit_one_sided_beta22_mollified_hinge_interior_curvature
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:31:32.206167+00:00
-- url     : https://prove2.me/submissions/c02a507b-eb00-4794-a9fe-79589b97d676

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ga_beta22_one_sided_hinge_interior_first_derivative_exact
import Theorems.Thm_AvramDividend_Classical_avram_ga_beta22_one_sided_hinge_interior_second_derivative_exact
open Set Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (b ε y : ℝ) (hε : 0 < ε) (hy : b < y) (hu : y < b + ε) :
    let Q : ℝ → ℝ := fun z : ℝ => if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
          (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
        else z - b - ε / 2
    deriv Q y = (3 / ε ^ 2) * (y - b) ^ 2 - (2 / ε ^ 3) * (y - b) ^ 3 ∧
    iteratedDeriv 2 Q y = (6 / ε ^ 2) * (y - b) - (6 / ε ^ 3) * (y - b) ^ 2 ∧
    0 ≤ iteratedDeriv 2 Q y := by
  let Q : ℝ → ℝ := fun z =>
    if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2
  change deriv Q y = (3 / ε ^ 2) * (y - b) ^ 2 -
      (2 / ε ^ 3) * (y - b) ^ 3 ∧
    iteratedDeriv 2 Q y = (6 / ε ^ 2) * (y - b) -
      (6 / ε ^ 3) * (y - b) ^ 2 ∧ 0 ≤ iteratedDeriv 2 Q y
  have hfirst := avram_ga_beta22_one_sided_hinge_interior_first_derivative_exact
    b ε y hε hy hu
  have hsecond := avram_ga_beta22_one_sided_hinge_interior_second_derivative_exact
    b ε y hε hy hu
  refine ⟨hfirst, hsecond, ?_⟩
  rw [hsecond]
  rw [show (6 / ε ^ 2) * (y - b) - (6 / ε ^ 3) * (y - b) ^ 2 =
      6 * (y - b) * (ε - (y - b)) / ε ^ 3 by
        field_simp]
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hy.le))
      (by linarith)) (pow_nonneg hε.le _)
