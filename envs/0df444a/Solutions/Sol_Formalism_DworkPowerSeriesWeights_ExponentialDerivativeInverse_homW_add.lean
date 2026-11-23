-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.homW_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:33.811803+00:00
-- url     : https://prove2.me/submissions/b1ddb410-4564-4924-9304-aad1209d46ff

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
namespace Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
theorem _root_.solution {c : ℤ} {f g : MvPowerSeries ι K} (hf : HomW w c f) (hg : HomW w c g) :
    HomW w c (f + g) := by
  intro n hn
  rw [map_add] at hn
  by_cases h : MvPowerSeries.coeff n f = 0
  · rw [h, zero_add] at hn; exact hg n hn
  · exact hf n h
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
