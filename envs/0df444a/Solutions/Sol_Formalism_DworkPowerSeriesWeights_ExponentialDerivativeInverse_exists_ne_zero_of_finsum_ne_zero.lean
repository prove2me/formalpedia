-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.exists_ne_zero_of_finsum_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:33.836798+00:00
-- url     : https://prove2.me/submissions/170c5df6-30a0-43d3-8122-f2a0d293d8f5

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
namespace Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
theorem _root_.solution {α : Type w} {g : α → K} (h : ∑ᶠ i, g i ≠ 0) :
    ∃ i, g i ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (finsum_eq_zero_of_forall_eq_zero hc)
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
