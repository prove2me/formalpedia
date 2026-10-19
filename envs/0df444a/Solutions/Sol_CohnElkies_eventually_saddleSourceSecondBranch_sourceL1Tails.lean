-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceSecondBranch_sourceL1Tails
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/27e42dcc-daec-495f-89c7-d79722295893

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_saddleSource_secondBranch_weighted_integrable
import Theorems.Thm_CohnElkies_eventually_saddleSource_secondBranch_uniform_tail
import Theorems.Thm_CohnElkies_eventually_saddleSourceSecondBranch_sourceL1Tails_of_uniform_tail

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
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ δ : ℝ, ε / 2 ≤ δ →
            (Real.sqrt
                (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
              (∫ T : ℝ in saddleGaussianTailSet
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                ‖saddleSourceCenteredPlusIntegrand
                    ε ℓ (1 + δ)
                    (saddleSourceStationaryLogRadius
                      ε ℓ (1 + δ)) T‖) <
              κ * ‖plusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖) ∧
            (Real.sqrt
                (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
              (∫ T : ℝ in saddleGaussianTailSet
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                ‖saddleSourceCenteredMinusIntegrand
                    ε ℓ (1 + δ)
                    (saddleSourceStationaryLogRadius
                      ε ℓ (1 + δ)) T‖) <
              κ * ‖minusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖) := by
  apply eventually_saddleSourceSecondBranch_sourceL1Tails_of_uniform_tail
    eventually_saddleSource_secondBranch_weighted_integrable
  simpa [saddleSourceSecondBranchCentralRadius] using!
    eventually_saddleSource_secondBranch_uniform_tail
end CohnElkies
