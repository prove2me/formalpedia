-- Prove2me | solution 1 for CohnElkies.stripHolomorphicPoissonKernel_eq_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/1bca3b51-afc4-4832-bf4d-955260f8a1f1

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) (σ s y : ℝ) :
    stripHolomorphicPoissonKernel ℓ
        ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y =
      stripComplexPoissonKernel σ ((s - y) / ℓ) / (ℓ : ℂ) := by
  have hℓc : (ℓ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hargument :
      ((Real.pi : ℂ) *
          (((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) -
            (y : ℂ) + Complex.I * (ℓ : ℂ))) /
            (2 * (ℓ : ℂ)) =
        ((Real.pi * ((s - y) / ℓ) / 2 : ℝ) : ℂ) +
          Complex.I * ((stripAngle σ : ℝ) : ℂ) := by
    unfold stripAngle
    push_cast
    field_simp [hℓc]
    ring
  unfold stripHolomorphicPoissonKernel stripComplexPoissonKernel
  rw [hargument]
end CohnElkies
