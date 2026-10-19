-- Prove2me | solution 1 for CohnElkies.eventually_plusSaddleProfile_re_pos_at_secondBranchSaddles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/a34fd406-eb37-48d2-b2eb-3079ca487537

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_saddleResidue_dimension_half
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_secondBranch_pos
import Theorems.Thm_CohnElkies_saddleSourceStationaryLogRadius_eq_saddleLogRadius
import Theorems.Thm_CohnElkies_eventually_saddleSourceSecondBranch_fullGaussianErrors
import Theorems.Thm_CohnElkies_plusSaddleProfile_re_pos_at_sourceSaddle_of_gaussian_error
import Theorems.Thm_CohnElkies_saddleSourceGaussianPlusIntegrand_integral_re_eq_norm

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ u : ℝ, 1 + ε / 2 ≤ u →
          0 < (plusSaddleProfile ε ((d : ℝ) / 2)
            (Real.exp (saddleLogRadius ε d u))).re := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_secondBranch_pos,
    eventually_saddleSourceSecondBranch_fullGaussianErrors]
    with ε hε horder hvariance hfull
  change 0 < ε at hε
  have hdimension :=
    tendsto_saddleResidue_dimension_half.eventually hfull
  filter_upwards [hdimension,
    eventually_gt_atTop (0 : ℕ)] with d hdimen hd
  intro u hu
  let δ : ℝ := u - 1
  have hδ : ε / 2 ≤ δ := by
    try dsimp [δ]
    linarith
  have hidentity : 1 + δ = u := by
    try dsimp [δ]
    ring
  have hulower : -1 < u := by linarith
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  have hV : 0 <
      saddleSourceGaussianVariance ε ((d : ℝ) / 2) u := by
    simpa only [hidentity] using!
      hvariance ((d : ℝ) / 2) hℓ δ hδ
  have herr := (hdimen δ hδ).1
  rw [hidentity] at herr
  have herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ((d : ℝ) / 2) u
            (saddleLogRadius ε d u) T) -
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ((d : ℝ) / 2) u T)‖ <
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand
            ε ((d : ℝ) / 2) u T).re := by
    rw [saddleSourceGaussianPlusIntegrand_integral_re_eq_norm
      hε hulower]
    simpa [saddleSourceStationaryLogRadius_eq_saddleLogRadius] using! herr
  exact plusSaddleProfile_re_pos_at_sourceSaddle_of_gaussian_error
    hε hd hulower horder hV herror
end CohnElkies
