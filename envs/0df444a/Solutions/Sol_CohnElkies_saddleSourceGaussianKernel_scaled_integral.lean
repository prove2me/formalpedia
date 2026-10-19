-- Prove2me | solution 1 for CohnElkies.saddleSourceGaussianKernel_scaled_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/2fa5542a-a27c-433f-9424-c6968156b2bd

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceGaussianKernel_integral

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
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u) :
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
        (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) =
      Real.sqrt (2 * Real.pi) := by
  let V : ℝ := saddleSourceGaussianVariance ε ℓ u
  have hV' : 0 < V := hV
  have hproduct : 0 < ℓ * V := mul_pos hℓ hV
  rw [saddleSourceGaussianKernel_integral]
  change
    Real.sqrt (ℓ * V) * Real.sqrt (Real.pi / (ℓ * V / 2)) =
      Real.sqrt (2 * Real.pi)
  rw [← Real.sqrt_mul hproduct.le]
  congr 1
  field_simp [hℓ.ne', hV'.ne', hproduct.ne']
end CohnElkies
