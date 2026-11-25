-- Prove2me | solution 1 for Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.eta_determinant_comparison
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:22:48.126893+00:00
-- url     : https://prove2.me/submissions/abe8825b-2bf0-47f7-8641-444f580322cb

import Definitions.Def_Formalism_TruncatedSeriesCounting_LemmaDetPoly
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_BridgeDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.NG
universe u v w
open Formalism Formalism.TruncatedSeriesCounting Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
theorem _root_.solution : BridgeDet.{u, v, w} := by
  intro hP hB O _ _ X' G _ T' d _ _ R' ρ hρ hR g _ _ Θ
  refine hB O X' T' d R' ?_ g Θ
  intro m a s
  exact hP O (FractionRing O) X' G d T' ρ hρ m (fun i => (a i : X' → Matrix d d (FractionRing O)))
    (fun i => hR _ (a i).2) s
end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
