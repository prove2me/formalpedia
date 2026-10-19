-- Prove2me | solution 1 for CohnElkies.stripRegularizedHolomorphicPoissonKernel_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/65bbbd3e-7d63-4117-8f50-7881e42219fd

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripHolomorphicPoissonKernel_denominator_ne_zero

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
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    {y : ℝ} (hy : 0 ≤ y) :
    stripRegularizedHolomorphicPoissonKernel ℓ z y =
      Complex.I * stripSchwarzExponential ℓ z y /
        (2 * (ℓ : ℂ) * (stripSchwarzExponential ℓ z y - 1)) := by
  have hℓc : (ℓ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hden := stripHolomorphicPoissonKernel_denominator_ne_zero
    hℓ hz y
  let w := stripSchwarzExponential ℓ z y
  have hw : w - 1 ≠ 0 := by
    simpa [w, stripSchwarzExponential] using! hden
  unfold stripRegularizedHolomorphicPoissonKernel
    stripHolomorphicPoissonKernel
  rw [if_pos hy]
  change
    (Complex.I * ((w + 1) / (w - 1)) / 4) / (ℓ : ℂ) +
        Complex.I / ((4 * ℓ : ℝ) : ℂ) =
      Complex.I * w / (2 * (ℓ : ℂ) * (w - 1))
  rw [show ((4 * ℓ : ℝ) : ℂ) = 4 * (ℓ : ℂ) by push_cast; rfl]
  field_simp [hℓc, hw]
  ring
end CohnElkies
