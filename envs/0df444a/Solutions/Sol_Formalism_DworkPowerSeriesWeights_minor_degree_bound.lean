-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.minor_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:29:53.11731+00:00
-- url     : https://prove2.me/submissions/9ba748ff-38e1-4ced-adb1-021b863c10fa

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spMinor

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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : MinorDeg.{u} := by
  intro R _ m p top T mono hmono k
  classical
  refine spMinor top _ (fun i o => Fin.cases (o.elim 1 (fun _ => 0)) (fun i' => o.elim 0 (T i')) i)
    ?_ mono hmono k
  intro i c
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp [spV, Fintype.sum_option]
  · simp [spV, Fintype.sum_option]
end Formalism.DworkPowerSeriesWeights
