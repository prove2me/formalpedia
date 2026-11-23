-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.inSub_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:33.871952+00:00
-- url     : https://prove2.me/submissions/9feea7cf-8628-4c07-9ebb-a0648ba4ce05

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
variable {K : Type u} [NormedField K] {ι : Type v} {K0 : Subfield K}
namespace Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
theorem _root_.solution {f g : MvPowerSeries ι K} (hf : InSub K0 f) (hg : InSub K0 g) :
    InSub K0 (f + g) := fun n => by rw [map_add]; exact K0.add_mem (hf n) (hg n)
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
