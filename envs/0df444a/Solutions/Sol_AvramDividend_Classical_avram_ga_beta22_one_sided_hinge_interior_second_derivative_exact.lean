-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_beta22_one_sided_hinge_interior_second_derivative_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:31:19.167944+00:00
-- url     : https://prove2.me/submissions/45854138-ecbf-4cdb-bb28-0a0c173663c9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_beta22_one_sided_hinge_interior_first_derivative_exact
open Set Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (b ε y : ℝ) (hε : 0 < ε) (hy : b < y) (hu : y < b + ε) :
    iteratedDeriv 2 (fun z : ℝ => if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2) y =
      (6 / ε ^ 2) * (y - b) - (6 / ε ^ 3) * (y - b) ^ 2 := by
  let Q : ℝ → ℝ := fun z =>
    if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2
  change iteratedDeriv 2 Q y =
    (6 / ε ^ 2) * (y - b) - (6 / ε ^ 3) * (y - b) ^ 2
  have he : deriv Q =ᶠ[𝓝 y]
      (fun z : ℝ => (3 / ε ^ 2) * (z - b) ^ 2 -
        (2 / ε ^ 3) * (z - b) ^ 3) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hy, hu⟩] with z hz
    exact avram_ga_beta22_one_sided_hinge_interior_first_derivative_exact
      b ε z hε hz.1 hz.2
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq]
  have hb : HasDerivAt (fun t : ℝ => t - b) 1 y := by
    simpa using (hasDerivAt_id y).sub_const b
  convert (((hb.pow 2).const_mul (3 / ε ^ 2)).sub
    ((hb.pow 3).const_mul (2 / ε ^ 3))).deriv using 1 <;> first | rfl | ring
