-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.inSub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:52.071119+00:00
-- url     : https://prove2.me/submissions/d97af3df-5d63-4dd8-af88-2b24eb9e2b90

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
theorem _root_.solution : InSub K0 (1 : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact K0.one_mem
  · exact K0.zero_mem
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
