-- Prove2me | solution 1 for CohnElkies.saddle_inverse_sqrt_cube_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/10b7d83d-2321-4ad4-a34d-e350d26c4ade

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
    {q : ℝ} (hq : 0 < q) :
    (Real.sqrt (q / 6) ^ 3)⁻¹ ≤
      1 + (6 / q) ^ 3 := by
  let s : ℝ := Real.sqrt (q / 6)
  have hs : 0 < s := by
    try dsimp [s]
    positivity
  have hsquare : s ^ 2 = q / 6 := by
    try dsimp [s]
    rw [Real.sq_sqrt (by positivity)]
  have hcubed : (s ^ 2) ^ 3 = (q / 6) ^ 3 :=
    congrArg (fun x : ℝ => x ^ 3) hsquare
  have hidentity :
      ((s ^ 3)⁻¹) ^ 2 = (6 / q) ^ 3 := by
    field_simp [hq.ne', hs.ne']
    nlinarith [hcubed]
  have hnonnegative : 0 ≤ (s ^ 3)⁻¹ := by
    positivity
  change (s ^ 3)⁻¹ ≤ 1 + (6 / q) ^ 3
  rw [← hidentity]
  nlinarith [sq_nonneg ((s ^ 3)⁻¹ - (1 / 2 : ℝ))]
end CohnElkies
