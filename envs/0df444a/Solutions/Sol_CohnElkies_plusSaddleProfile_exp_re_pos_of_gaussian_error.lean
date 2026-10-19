-- Prove2me | solution 1 for CohnElkies.plusSaddleProfile_exp_re_pos_of_gaussian_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/b0ff76b5-f04b-4c37-a17c-43c62d25d401

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceCenteredPrefactor_pos
import Theorems.Thm_CohnElkies_plusSaddleProfile_exp_eq_centeredIntegral

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u v : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ <
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ℓ u T).re) :
    0 < (plusSaddleProfile ε ℓ (Real.exp v)).re := by
  have _hV : 0 < saddleSourceGaussianVariance ε ℓ u := hV
  let J : ℂ := ∫ T : ℝ,
    saddleSourceCenteredPlusIntegrand ε ℓ u v T
  let G : ℂ := ∫ T : ℝ,
    saddleSourceGaussianPlusIntegrand ε ℓ u T
  have hreal : |(J - G).re| ≤ ‖J - G‖ :=
    Complex.abs_re_le_norm _
  have hpositive : 0 < J.re := by
    change ‖J - G‖ < G.re at herror
    have hlower : -‖J - G‖ ≤ (J - G).re := by
      have := (neg_le_of_abs_le hreal)
      exact this
    rw [Complex.sub_re] at hlower
    linarith
  rw [plusSaddleProfile_exp_eq_centeredIntegral
    hε hℓ hu horder v]
  change 0 <
    ((saddleSourceCenteredPrefactor ε ℓ u v : ℂ) * J).re
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos
    (saddleSourceCenteredPrefactor_pos hℓ hu v)
    hpositive
end CohnElkies
