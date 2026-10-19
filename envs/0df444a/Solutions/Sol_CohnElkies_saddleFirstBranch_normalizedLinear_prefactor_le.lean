-- Prove2me | solution 1 for CohnElkies.saddleFirstBranch_normalizedLinear_prefactor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/51246558-63e1-41a6-b1ba-7e8136d9a917

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
    {ℓ V η C : ℝ}
    (hℓ : 0 < ℓ) (hV : 0 < V) (hη : 0 < η)
    (hC : 0 < C)
    (hupper : η * V ≤ C) :
    Real.sqrt (ℓ * V) / ℓ ≤
      Real.sqrt (C / (ℓ * η)) := by
  have hfrac : V / ℓ ≤ C / (ℓ * η) := by
    apply (div_le_div_iff₀ hℓ (mul_pos hℓ hη)).mpr
    have hscaled :=
      mul_le_mul_of_nonneg_left hupper hℓ.le
    nlinarith
  have hidentity :
      Real.sqrt (ℓ * V) / ℓ = Real.sqrt (V / ℓ) := by
    calc
      Real.sqrt (ℓ * V) / ℓ =
          Real.sqrt ((ℓ * V) / ℓ ^ 2) := by
            rw [Real.sqrt_div (mul_nonneg hℓ.le hV.le),
              Real.sqrt_sq_eq_abs,
              abs_of_pos hℓ]
      _ = Real.sqrt (V / ℓ) := by
            congr 1
            field_simp [hℓ.ne']
  rw [hidentity]
  exact (Real.sqrt_le_sqrt_iff
    (div_pos hC (mul_pos hℓ hη)).le).mpr hfrac
end CohnElkies
