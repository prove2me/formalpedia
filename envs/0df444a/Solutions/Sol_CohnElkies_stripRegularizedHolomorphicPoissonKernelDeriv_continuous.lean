-- Prove2me | solution 1 for CohnElkies.stripRegularizedHolomorphicPoissonKernelDeriv_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/8830f737-9c4e-4832-95b5-8827c209b1b0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripSchwarzExponential_continuous
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
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) :
    Continuous
      (fun y : ℝ => stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y) := by
  have hcoordinate := stripSchwarzExponential_continuous ℓ z
  unfold stripRegularizedHolomorphicPoissonKernelDeriv
  apply Continuous.div
  · exact
      ((continuous_const.mul continuous_const).mul hcoordinate).neg
  · exact continuous_const.mul
      ((hcoordinate.sub continuous_const).pow 2)
  · intro y
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num)
        (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hℓ.ne'))
    · apply pow_ne_zero
      simpa [stripSchwarzExponential] using!
        stripHolomorphicPoissonKernel_denominator_ne_zero hℓ hz y
end CohnElkies
