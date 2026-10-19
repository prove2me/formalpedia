-- Prove2me | solution 1 for CohnElkies.eventually_minusSaddleProfile_re_neg_at_firstBranchSaddles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/3af785f4-d353-4e1e-9a15-1487640f0084

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_saddleResidue_dimension_half
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_firstBranch_pos
import Theorems.Thm_CohnElkies_saddleSourceStationaryLogRadius_eq_saddleLogRadius
import Theorems.Thm_CohnElkies_eventually_saddleSourceFirstBranch_fullGaussianErrors
import Theorems.Thm_CohnElkies_minusSaddleProfile_re_neg_at_sourceSaddle_of_gaussian_error
import Theorems.Thm_CohnElkies_saddleSourceGaussianMinusIntegrand_neg_integral_re_eq_norm
import Theorems.Thm_CohnElkies_saddleSource_positiveOrdinate_sourceScale

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
          1 + ε / 4 ≤ u →
            u ≤ 1 + ε / 2 →
              (minusSaddleProfile ε ((d : ℝ) / 2)
                (Real.exp (saddleLogRadius ε d u))).re < 0 := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_firstBranch_pos,
    eventually_saddleSourceFirstBranch_fullGaussianErrors]
    with ε hε horder hvariance hfull
  change 0 < ε at hε
  have hdimension :=
    tendsto_saddleResidue_dimension_half.eventually hfull
  filter_upwards [hdimension,
    eventually_gt_atTop (0 : ℕ)] with d hdimen hd
  intro u hulower hupper
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  have hu : -1 < u := by linarith
  have huone : 1 ≤ u := by linarith
  have hscale := saddleSource_positiveOrdinate_sourceScale hℓ huone
  have herr := (hdimen u hu hupper hscale).2 hulower
  have hV := hvariance ((d : ℝ) / 2) hℓ u hu hupper
  have herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredMinusIntegrand ε ((d : ℝ) / 2) u
            (saddleLogRadius ε d u) T) -
        (∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ((d : ℝ) / 2) u T)‖ <
        -(∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand
            ε ((d : ℝ) / 2) u T).re := by
    rw [saddleSourceGaussianMinusIntegrand_neg_integral_re_eq_norm
      hε hulower]
    simpa [saddleSourceStationaryLogRadius_eq_saddleLogRadius] using! herr
  exact minusSaddleProfile_re_neg_at_sourceSaddle_of_gaussian_error
    hε hd hu horder hV herror
end CohnElkies
