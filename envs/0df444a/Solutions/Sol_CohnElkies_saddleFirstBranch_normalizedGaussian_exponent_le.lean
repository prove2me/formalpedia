-- Prove2me | solution 1 for CohnElkies.saddleFirstBranch_normalizedGaussian_exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/10853238-a06c-4a0b-b5fa-681fbe7add79

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
    {ℓ V η c C z : ℝ}
    (hℓ : 0 < ℓ) (hV : 0 < V) (hη : 0 < η)
    (hc : 0 < c) (hC : 0 < C)
    (hupper : η * V ≤ C) :
    (c / (4 * C)) * z ^ 2 ≤
      ((c * ℓ / η) / 4) *
        (z / Real.sqrt (ℓ * V)) ^ 2 := by
  have hLV : 0 < ℓ * V := mul_pos hℓ hV
  have hinverse : 1 / C ≤ 1 / (η * V) := by
    exact (one_div_le_one_div hC (mul_pos hη hV)).mpr hupper
  have hscaled := mul_le_mul_of_nonneg_left hinverse
    (show 0 ≤ c * z ^ 2 / 4 by positivity)
  have hsquare :
      (z / Real.sqrt (ℓ * V)) ^ 2 =
        z ^ 2 / (ℓ * V) := by
    rw [div_pow, Real.sq_sqrt hLV.le]
  rw [hsquare]
  calc
    (c / (4 * C)) * z ^ 2 =
        (c * z ^ 2 / 4) * (1 / C) := by ring
    _ ≤ (c * z ^ 2 / 4) * (1 / (η * V)) := hscaled
    _ = ((c * ℓ / η) / 4) *
          (z ^ 2 / (ℓ * V)) := by
      field_simp [hℓ.ne', hV.ne', hη.ne']
end CohnElkies
