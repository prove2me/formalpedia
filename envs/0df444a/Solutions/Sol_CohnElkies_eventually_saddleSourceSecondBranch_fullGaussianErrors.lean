-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceSecondBranch_fullGaussianErrors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/a1dfb116-b116-4cac-bb75-66e4fc8eb51e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_saddleSourceSecondBranch_fullGaussianErrors_of_sourceL1
import Theorems.Thm_CohnElkies_eventually_saddleSourceSecondBranch_sourceL1Tails

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ ℓ : ℝ in atTop,
        ∀ δ : ℝ, ε / 2 ≤ δ →
          (‖(∫ T : ℝ,
              saddleSourceCenteredPlusIntegrand ε ℓ (1 + δ)
                (saddleSourceStationaryLogRadius
                  ε ℓ (1 + δ)) T) -
            (∫ T : ℝ,
              saddleSourceGaussianPlusIntegrand ε ℓ (1 + δ) T)‖ <
            ‖plusPolynomial ε
              (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ (1 + δ) T)) ∧
          (‖(∫ T : ℝ,
              saddleSourceCenteredMinusIntegrand ε ℓ (1 + δ)
                (saddleSourceStationaryLogRadius
                  ε ℓ (1 + δ)) T) -
            (∫ T : ℝ,
              saddleSourceGaussianMinusIntegrand ε ℓ (1 + δ) T)‖ <
            ‖minusPolynomial ε
              (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ (1 + δ) T)) :=
  eventually_saddleSourceSecondBranch_fullGaussianErrors_of_sourceL1
    eventually_saddleSourceSecondBranch_sourceL1Tails
end CohnElkies
