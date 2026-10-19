-- Prove2me | solution 1 for CohnElkies.stripRegularizedHolomorphicPoissonKernel_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/06300c19-8a32-4a6f-ac56-175896e69c59

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripSchwarzExponential_hasDerivAt
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
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    HasDerivAt
      (fun w : ℂ => stripRegularizedHolomorphicPoissonKernel ℓ w y)
      (-(Complex.I * (Real.pi : ℂ) *
          stripSchwarzExponential ℓ z y) /
        (4 * (ℓ : ℂ) ^ 2 *
          (stripSchwarzExponential ℓ z y - 1) ^ 2)) z := by
  have hℓc : (ℓ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hden : stripSchwarzExponential ℓ z y - 1 ≠ 0 := by
    simpa [stripSchwarzExponential] using!
      stripHolomorphicPoissonKernel_denominator_ne_zero hℓ hz y
  have hexp := stripSchwarzExponential_hasDerivAt ℓ z y
  have hratio :=
    (hexp.add_const 1).div (hexp.sub_const 1) hden
  have hkernel :=
    ((((hratio.const_mul Complex.I).div_const (4 : ℂ)).div_const
      (ℓ : ℂ))).add_const
      ((if 0 ≤ y then Complex.I else -Complex.I) /
        ((4 * ℓ : ℝ) : ℂ))
  unfold stripRegularizedHolomorphicPoissonKernel
    stripHolomorphicPoissonKernel
  convert! hkernel using 1
  field_simp [hℓc, hden]
  ring
end CohnElkies
