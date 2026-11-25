-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.pure_weight_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:32:04.209073+00:00
-- url     : https://prove2.me/submissions/e9a600e3-ad9b-4726-b7a0-601dc43e4888

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spCore

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
theorem _root_.solution : PureFormula.{u, v} := by
  intro K _ l d N0 N1 _ _ ι _ _ lt M hM be i j α β hij
  unfold bSum pureMon
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  exact spCore (N := fun s k => M (s, ab.1, ab.2) k) (fun s k h => hM _ _ h) be i j _ _ hij
end Formalism.DworkPowerSeriesWeights
