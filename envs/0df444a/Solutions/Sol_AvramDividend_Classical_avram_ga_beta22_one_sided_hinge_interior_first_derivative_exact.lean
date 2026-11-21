-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_beta22_one_sided_hinge_interior_first_derivative_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:17:47.311524+00:00
-- url     : https://prove2.me/submissions/ab1eba62-9b60-44b1-99ce-16ffc97a7876

import Mathlib
open Set Filter Topology
noncomputable section

theorem solution
    (b ε y : ℝ) (hε : 0 < ε) (hy : b < y) (hu : y < b + ε) :
    deriv (fun z : ℝ => if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2) y =
      (3 / ε ^ 2) * (y - b) ^ 2 -
        (2 / ε ^ 3) * (y - b) ^ 3 := by
  let Q : ℝ → ℝ := fun z =>
    if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2
  change deriv Q y =
    (3 / ε ^ 2) * (y - b) ^ 2 - (2 / ε ^ 3) * (y - b) ^ 3
  have he : Q =ᶠ[𝓝 y]
      (fun t : ℝ => (1 / ε ^ 2) * (t - b) ^ 3 -
        (1 / (2 * ε ^ 3)) * (t - b) ^ 4) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hy, hu⟩] with t ht
    dsimp [Q]
    rw [if_neg (not_le.mpr ht.1), if_pos (le_of_lt ht.2)]
  rw [he.deriv_eq]
  have hb : HasDerivAt (fun t : ℝ => t - b) 1 y := by
    simpa using (hasDerivAt_id y).sub_const b
  convert (((hb.pow 3).const_mul (1 / ε ^ 2)).sub
    ((hb.pow 4).const_mul (1 / (2 * ε ^ 3)))).deriv
    using 1 <;> first | rfl | ring
