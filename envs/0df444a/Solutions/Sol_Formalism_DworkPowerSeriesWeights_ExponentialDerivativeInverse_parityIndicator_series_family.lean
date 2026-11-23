-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.parityIndicator_series_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:13.213314+00:00
-- url     : https://prove2.me/submissions/9d0cbfea-80b3-44e6-b55d-5abba25f6efd

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_inSub_X
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_homW_X

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
variable {K : Type u} [NormedField K] {d : ℕ}
variable {K0 : Subfield K} {l : ℕ}
namespace Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
theorem _root_.solution : Fam K0 l (s2' (K := K) (d := d)) := by
  intro s
  unfold s2'
  split_ifs
  · exact ⟨by simp, inSub_X _, homW_X (false, s)⟩
  · exact ⟨by simp, inSub_X _, homW_X (true, s)⟩
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
