-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB30_quadratic_piecewise_positive_jets
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:03:19.35419+00:00
-- url     : https://prove2.me/submissions/2b0e1c28-8d0c-4365-93ff-21aae5cb17f2

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section
theorem AvramDividend.Classical.avram_gbB30_quadratic_piecewise_positive_jets (y : ℝ) (hy : 0 < y) :
    deriv (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) y = 2 - 8 * y ∧
      iteratedDeriv 2 (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) y = -8 := by
  constructor
  · have h : (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) =ᶠ[nhds y]
        (fun z : ℝ => 2 * z - 4 * z ^ 2) := by
      filter_upwards [lt_mem_nhds hy] with z hz
      simp [not_lt.mpr hz.le]
    rw [h.deriv_eq]
    have : HasDerivAt (fun z : ℝ => 2 * z - 4 * z ^ 2) (2 * 1 - 4 * (2 * y ^ 1 * 1)) y :=
      ((hasDerivAt_id y).const_mul 2).sub (((hasDerivAt_id y).pow 2).const_mul 4)
    rw [this.deriv]; ring
  · have h : (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) =ᶠ[nhds y]
        (fun z : ℝ => 2 * z - 4 * z ^ 2) := by
      filter_upwards [lt_mem_nhds hy] with z hz
      simp [not_lt.mpr hz.le]
    rw [h.iteratedDeriv_eq]
    have hd : deriv (fun z : ℝ => 2 * z - 4 * z ^ 2) = fun z => 2 - 8 * z := by
      funext z
      have : HasDerivAt (fun z : ℝ => 2 * z - 4 * z ^ 2) (2 * 1 - 4 * (2 * z ^ 1 * 1)) z :=
        ((hasDerivAt_id z).const_mul 2).sub (((hasDerivAt_id z).pow 2).const_mul 4)
      rw [this.deriv]; ring
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
    have : HasDerivAt (fun z : ℝ => 2 - 8 * z) (-(8 * 1)) y :=
      ((hasDerivAt_id y).const_mul 8).const_sub 2
    rw [this.deriv]; ring

theorem solution (y : ℝ) (hy : 0 < y) :
    deriv (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) y = 2 - 8 * y ∧
      iteratedDeriv 2 (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) y = -8 := by
  constructor
  · have h : (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) =ᶠ[nhds y]
        (fun z : ℝ => 2 * z - 4 * z ^ 2) := by
      filter_upwards [lt_mem_nhds hy] with z hz
      simp [not_lt.mpr hz.le]
    rw [h.deriv_eq]
    have : HasDerivAt (fun z : ℝ => 2 * z - 4 * z ^ 2) (2 * 1 - 4 * (2 * y ^ 1 * 1)) y :=
      ((hasDerivAt_id y).const_mul 2).sub (((hasDerivAt_id y).pow 2).const_mul 4)
    rw [this.deriv]; ring
  · have h : (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2) =ᶠ[nhds y]
        (fun z : ℝ => 2 * z - 4 * z ^ 2) := by
      filter_upwards [lt_mem_nhds hy] with z hz
      simp [not_lt.mpr hz.le]
    rw [h.iteratedDeriv_eq]
    have hd : deriv (fun z : ℝ => 2 * z - 4 * z ^ 2) = fun z => 2 - 8 * z := by
      funext z
      have : HasDerivAt (fun z : ℝ => 2 * z - 4 * z ^ 2) (2 * 1 - 4 * (2 * z ^ 1 * 1)) z :=
        ((hasDerivAt_id z).const_mul 2).sub (((hasDerivAt_id z).pow 2).const_mul 4)
      rw [this.deriv]; ring
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
    have : HasDerivAt (fun z : ℝ => 2 - 8 * z) (-(8 * 1)) y :=
      ((hasDerivAt_id y).const_mul 8).const_sub 2
    rw [this.deriv]; ring

