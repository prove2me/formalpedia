-- Prove2me | solution 1 for CohnElkies.eventually_plusSaddleProfile_re_pos_at_firstBranchSaddles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/4957584c-6cd3-4186-bccc-c63f4eed436f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_saddleResidue_dimension_half
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_firstBranch_pos
import Theorems.Thm_CohnElkies_saddleSourceStationaryLogRadius_eq_saddleLogRadius
import Theorems.Thm_CohnElkies_eventually_saddleSourceFirstBranch_fullGaussianErrors
import Theorems.Thm_CohnElkies_eventually_saddleSmallRadiusStarOrdinate_gt_neg_one
import Theorems.Thm_CohnElkies_plusSaddleProfile_re_pos_at_sourceSaddle_of_gaussian_error
import Theorems.Thm_CohnElkies_saddleSourceGaussianPlusIntegrand_integral_re_eq_norm
import Theorems.Thm_CohnElkies_saddleSmallRadiusStarOrdinate_sourceScale

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
        ∀ u : ℝ,
          saddleSmallRadiusStarOrdinate ε d ≤ u →
            u ≤ 1 + ε / 2 →
              0 < (plusSaddleProfile ε ((d : ℝ) / 2)
                (Real.exp (saddleLogRadius ε d u))).re := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_firstBranch_pos,
    eventually_saddleSourceFirstBranch_fullGaussianErrors]
    with ε hε horder hvariance hfull
  change 0 < ε at hε
  have hdimension :=
    tendsto_saddleResidue_dimension_half.eventually hfull
  filter_upwards [hdimension,
    eventually_saddleSmallRadiusStarOrdinate_gt_neg_one ε,
    eventually_gt_atTop (0 : ℕ)]
    with d hdimen hstar hd
  intro u hu hupper
  have hulower : -1 < u := hstar.trans_le hu
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  have hscale := saddleSmallRadiusStarOrdinate_sourceScale hd ε hu
  have herr := (hdimen u hulower hupper hscale).1
  have hV := hvariance ((d : ℝ) / 2) hℓ u hulower hupper
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
