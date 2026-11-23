-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.wsum_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:20.420493+00:00
-- url     : https://prove2.me/submissions/106206e2-e44c-42a3-b2cd-5468fc0d14b2

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
theorem _root_.solution (w : ι → ℤ) (m n : ι →₀ ℕ) : wsum w (m + n) = wsum w m + wsum w n := by
  classical
  unfold wsum
  exact Finsupp.sum_add_index' (fun i => by simp) (fun i a b => by push_cast; ring)
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
