-- Prove2me | solution 1 for CohnElkies.saddleSource_cubic_window_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/0c465c76-89cd-4cc9-9696-d42185a385d1

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
    {ℓ V M C z T : ℝ}
    (hℓ : 0 < ℓ) (hV : 0 < V)
    (hC : 0 ≤ C) (hz : 0 ≤ z)
    (hM : M ≤ C * V)
    (hT : |T| ≤ z / Real.sqrt (ℓ * V)) :
    (ℓ * M / 6) * |T| ^ 3 ≤
      (C / 6) * z ^ 3 / Real.sqrt (ℓ * V) := by
  have _hz : 0 ≤ z := hz
  have hs : 0 < Real.sqrt (ℓ * V) :=
    Real.sqrt_pos.2 (mul_pos hℓ hV)
  calc
    (ℓ * M / 6) * |T| ^ 3 ≤
        (ℓ * (C * V) / 6) * |T| ^ 3 := by
      gcongr
    _ ≤ (ℓ * (C * V) / 6) *
        (z / Real.sqrt (ℓ * V)) ^ 3 := by
      gcongr
    _ = (C / 6) * z ^ 3 / Real.sqrt (ℓ * V) := by
      field_simp [hs.ne']
      rw [Real.sq_sqrt (mul_nonneg hℓ.le hV.le)]
      ring
end CohnElkies
