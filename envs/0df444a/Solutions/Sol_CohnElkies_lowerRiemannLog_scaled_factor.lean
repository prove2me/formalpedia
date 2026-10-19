-- Prove2me | solution 1 for CohnElkies.lowerRiemannLog_scaled_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/3e7e8208-0496-4ec1-8d19-92ee462cc7b1

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ T : ℝ} (hℓ : 0 < ℓ) (j : ℝ) :
    Real.sqrt (j ^ 2 + (ℓ * T / 2) ^ 2) =
      ℓ * Real.sqrt ((j / ℓ) ^ 2 + T ^ 2 / 4) := by
  have hinside :
      j ^ 2 + (ℓ * T / 2) ^ 2 =
        ℓ ^ 2 * ((j / ℓ) ^ 2 + T ^ 2 / 4) := by
    field_simp [hℓ.ne']
    ring
  rw [hinside, Real.sqrt_mul (sq_nonneg ℓ),
    Real.sqrt_sq_eq_abs, abs_of_pos hℓ]
end CohnElkies
