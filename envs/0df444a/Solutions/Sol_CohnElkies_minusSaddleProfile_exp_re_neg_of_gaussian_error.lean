-- Prove2me | solution 1 for CohnElkies.minusSaddleProfile_exp_re_neg_of_gaussian_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/ad7fa227-882c-4bc3-91f1-7a7775ef97c0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceCenteredPrefactor_pos
import Theorems.Thm_CohnElkies_minusSaddleProfile_exp_eq_centeredIntegral

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
          saddleSourceCenteredMinusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ <
        -(∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ℓ u T).re) :
    (minusSaddleProfile ε ℓ (Real.exp v)).re < 0 := by
  have _hV : 0 < saddleSourceGaussianVariance ε ℓ u := hV
  let J : ℂ := ∫ T : ℝ,
    saddleSourceCenteredMinusIntegrand ε ℓ u v T
  let G : ℂ := ∫ T : ℝ,
    saddleSourceGaussianMinusIntegrand ε ℓ u T
  have hreal : |(J - G).re| ≤ ‖J - G‖ :=
    Complex.abs_re_le_norm _
  have hnegative : J.re < 0 := by
    change ‖J - G‖ < -G.re at herror
    have hupper : (J - G).re ≤ ‖J - G‖ :=
      (le_abs_self _).trans hreal
    rw [Complex.sub_re] at hupper
    linarith
  rw [minusSaddleProfile_exp_eq_centeredIntegral
    hε hℓ hu horder v]
  change
    ((saddleSourceCenteredPrefactor ε ℓ u v : ℂ) * J).re < 0
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg
    (saddleSourceCenteredPrefactor_pos hℓ hu v)
    hnegative
end CohnElkies
