-- Prove2me | solution 1 for CohnElkies.saddleSourceCenteredMinusIntegrand_centralGaussianError_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/a0770776-6f3c-44e2-b716-3c05d15402e7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceCenteredMinusIntegrand_integrable
import Theorems.Thm_CohnElkies_saddleSourceCenteredPolynomial_centralGaussianError_le

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
    {ε ℓ u R q p : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hR : 0 ≤ R) (hq : 0 ≤ q) (hqone : q ≤ 1)
    (hp : 0 ≤ p)
    (hcubic : ∀ T : ℝ, |T| ≤ R →
      (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤ q)
    (hpoly : ∀ T : ℝ, |T| ≤ R →
      ‖minusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ)) -
        minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
          p * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖) :
    ‖∫ T : ℝ in Icc (-R) R,
        (saddleSourceCenteredMinusIntegrand ε ℓ u
          (saddleSourceStationaryLogRadius ε ℓ u) T -
            saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ ≤
      (2 * q + (1 + 2 * q) * p) *
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := by
  exact saddleSourceCenteredPolynomial_centralGaussianError_le
    hε hℓ hu horder hmargin hV hR hq hqone hp
    (minusPolynomial ε)
    (saddleSourceCenteredMinusIntegrand_integrable
      hε hℓ hu horder (saddleSourceStationaryLogRadius ε ℓ u))
    hcubic hpoly
end CohnElkies
