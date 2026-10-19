-- Prove2me | solution 1 for CohnElkies.saddleFirstBranch_normalizedGaussian_prefactor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/41a66ab8-d2e9-4694-94eb-e84ee11f5aa7

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ V η c C : ℝ}
    (hℓ : 0 < ℓ) (hV : 0 < V) (hη : 0 < η)
    (hc : 0 < c)
    (hupper : η * V ≤ C) :
    Real.sqrt (ℓ * V) *
        Real.sqrt (Real.pi / ((c * ℓ / η) / 4)) ≤
      2 * Real.sqrt (Real.pi * C / c) := by
  have hinside :
      (ℓ * V) * (Real.pi / ((c * ℓ / η) / 4)) ≤
        4 * (Real.pi * C / c) := by
    calc
      (ℓ * V) * (Real.pi / ((c * ℓ / η) / 4)) =
          4 * Real.pi * (η * V) / c := by
            field_simp [hc.ne', hℓ.ne', hη.ne']
      _ ≤ 4 * Real.pi * C / c := by
        gcongr
      _ = 4 * (Real.pi * C / c) := by ring
  rw [← Real.sqrt_mul (mul_nonneg hℓ.le hV.le)]
  calc
    Real.sqrt
        ((ℓ * V) *
          (Real.pi / ((c * ℓ / η) / 4))) ≤
      Real.sqrt (4 * (Real.pi * C / c)) :=
        Real.sqrt_le_sqrt hinside
    _ = 2 * Real.sqrt (Real.pi * C / c) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
end CohnElkies
