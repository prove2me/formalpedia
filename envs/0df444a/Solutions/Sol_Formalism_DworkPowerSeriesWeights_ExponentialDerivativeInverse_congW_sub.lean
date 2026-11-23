-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.congW_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:44.701796+00:00
-- url     : https://prove2.me/submissions/70a296d3-716e-4ead-9f24-4f75deb5f6fe

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
variable {K : Type u} [NormedField K] {ι : Type v}
variable {w : ι → ℤ}
variable {N : ℤ}
namespace Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
theorem _root_.solution {f g : MvPowerSeries ι K} (hf : CongW N w f) (hg : CongW N w g) :
    CongW N w (f - g) := by
  intro n hn
  rw [map_sub] at hn
  by_cases h : MvPowerSeries.coeff n f = 0
  · rw [h, zero_sub, neg_ne_zero] at hn; exact hg n hn
  · exact hf n h
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
