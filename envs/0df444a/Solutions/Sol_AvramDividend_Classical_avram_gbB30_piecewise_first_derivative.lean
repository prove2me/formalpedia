-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB30_piecewise_first_derivative
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:03:17.236652+00:00
-- url     : https://prove2.me/submissions/548a2b0b-19ba-47ba-9a74-546ddf0116c6

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section
theorem AvramDividend.Classical.avram_gbB30_piecewise_first_derivative (y : ℝ) (hy : 0 < y) :
    deriv (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) y = 2 - 8 * y := by
  have h : (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) =ᶠ[nhds y]
      (fun z : ℝ => 2 * z - 4 * z ^ 2) := by
    filter_upwards [lt_mem_nhds hy] with z hz
    simp [not_lt.mpr hz.le]
  rw [h.deriv_eq]
  have : HasDerivAt (fun z : ℝ => 2 * z - 4 * z ^ 2) (2 * 1 - 4 * (2 * y ^ 1 * 1)) y :=
    ((hasDerivAt_id y).const_mul 2).sub (((hasDerivAt_id y).pow 2).const_mul 4)
  rw [this.deriv]; ring

theorem solution (y : ℝ) (hy : 0 < y) :
    deriv (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) y = 2 - 8 * y := by
  have h : (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) =ᶠ[nhds y]
      (fun z : ℝ => 2 * z - 4 * z ^ 2) := by
    filter_upwards [lt_mem_nhds hy] with z hz
    simp [not_lt.mpr hz.le]
  rw [h.deriv_eq]
  have : HasDerivAt (fun z : ℝ => 2 * z - 4 * z ^ 2) (2 * 1 - 4 * (2 * y ^ 1 * 1)) y :=
    ((hasDerivAt_id y).const_mul 2).sub (((hasDerivAt_id y).pow 2).const_mul 4)
  rw [this.deriv]; ring

