-- Prove2me | solution 2 for CohnElkies.saddleFirstBranch_normalizedLinear_prefactor_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:12.717491+00:00
-- url     : https://prove2.me/submissions/4b1f220f-4f4f-4d11-b9ed-cd30c7313b6f

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


theorem solution
    {ℓ V η C : ℝ}
    (hℓ : 0 < ℓ) (hV : 0 < V) (hη : 0 < η)
    (hC : 0 < C)
    (hupper : η * V ≤ C) :
    Real.sqrt (ℓ * V) / ℓ ≤
      Real.sqrt (C / (ℓ * η)) := by
  rw [Real.le_sqrt (by positivity) (by positivity), div_pow, Real.sq_sqrt (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hupper (sq_nonneg ℓ)]

