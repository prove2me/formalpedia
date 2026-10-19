-- Prove2me | solution 1 for CohnElkies.saddleExpSeries_polynomialMoment_sum_range_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/40e9f39b-983d-4cef-ba62-86d0ed3d8cf1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleExpSeries_polynomialMoment_hasSum

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ((n : ℝ) + (n : ℝ) ^ 2) *
        (y ^ n / (n.factorial : ℝ))) ≤
      (2 * y + y ^ 2) * Real.exp y := by
  exact sum_le_hasSum (Finset.range N)
    (fun n _ => by positivity)
    (saddleExpSeries_polynomialMoment_hasSum y)
end CohnElkies
