-- Prove2me | solution 1 for CohnElkies.exists_saddleSource_central_error_tolerance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/856440b6-9525-4cb0-9005-c6e2adae1e89

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧
      2 * q + (1 + 2 * q) * q < κ := by
  let q : ℝ := min (1 / 4 : ℝ) (κ / 8)
  have hq : 0 < q := by
    try dsimp [q]
    positivity
  have hquarter : q ≤ (1 / 4 : ℝ) := min_le_left _ _
  have hk : q ≤ κ / 8 := min_le_right _ _
  refine ⟨q, hq, by linarith, ?_⟩
  nlinarith [mul_nonneg hq.le
    (sub_nonneg.mpr hquarter)]
end CohnElkies
