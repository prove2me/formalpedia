-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_annular_fractional_decay_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:47:22.024859+00:00
-- url     : https://prove2.me/submissions/28c11750-d3a5-44a6-b784-1ee79a6bbe4a

import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_annular_fractional_decay_le_geometric

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (H : ℕ) {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (∑ j ∈ Finset.range (H + 1),
        (2 * Real.exp (-2 * (j : ℝ) ^ 2)) ^ (1 - theta)) ≤
      (2 : ℝ) ^ (1 - theta) *
        (1 - Real.exp (-2 * (1 - theta)))⁻¹ := by
  let q := Real.exp (-2 * (1 - theta))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom :
      (∑ j ∈ Finset.range (H + 1), q ^ j) ≤ (1 - q)⁻¹ := by
    have hsummable := summable_geometric_of_lt_one hq0 hq1
    have hfinite := hsummable.sum_le_tsum (Finset.range (H + 1))
      (fun j hj => pow_nonneg hq0 j)
    rw [tsum_geometric_of_lt_one hq0 hq1] at hfinite
    exact hfinite
  calc
    (∑ j ∈ Finset.range (H + 1),
        (2 * Real.exp (-2 * (j : ℝ) ^ 2)) ^ (1 - theta)) ≤
        ∑ j ∈ Finset.range (H + 1),
          (2 : ℝ) ^ (1 - theta) * q ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      simpa [q] using annular_fractional_decay_le_geometric
        (j := j) htheta0 htheta1
    _ = (2 : ℝ) ^ (1 - theta) *
          ∑ j ∈ Finset.range (H + 1), q ^ j := by
      rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ (1 - theta) * (1 - q)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hgeom (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (1 - theta) *
          (1 - Real.exp (-2 * (1 - theta)))⁻¹ := by rfl
end CollatzEndpointTransport.FixedTotal
