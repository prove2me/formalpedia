-- Prove2me | solution 1 for CohnElkies.stripRegularizedHolomorphicPoissonKernel_continuousOn_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/828d670f-3d65-45fb-a180-09f09580b986

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripSchwarzExponential_continuous
import Theorems.Thm_CohnElkies_stripHolomorphicPoissonKernel_denominator_ne_zero
import Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernel_of_nonneg

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
    ContinuousOn
      (fun y : ℝ => stripRegularizedHolomorphicPoissonKernel ℓ z y)
      (Ioi (0 : ℝ)) := by
  have hcoordinate := stripSchwarzExponential_continuous ℓ z
  have hden : ∀ y : ℝ,
      stripSchwarzExponential ℓ z y - 1 ≠ 0 := by
    intro y
    simpa [stripSchwarzExponential] using!
      stripHolomorphicPoissonKernel_denominator_ne_zero hℓ hz y
  have hform :
      Continuous (fun y : ℝ =>
        Complex.I * stripSchwarzExponential ℓ z y /
          (2 * (ℓ : ℂ) *
            (stripSchwarzExponential ℓ z y - 1))) := by
    apply (continuous_const.mul hcoordinate).div
      (continuous_const.mul (hcoordinate.sub continuous_const))
    intro y
    exact mul_ne_zero
      (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
        (Complex.ofReal_ne_zero.mpr hℓ.ne'))
      (hden y)
  refine hform.continuousOn.congr ?_
  intro y hy
  exact stripRegularizedHolomorphicPoissonKernel_of_nonneg
    hℓ hz (mem_Ioi.mp hy).le
end CohnElkies
