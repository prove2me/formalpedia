-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.frobenius_congruence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:32:48.253735+00:00
-- url     : https://prove2.me/submissions/2e416e97-9200-4170-bf58-ed8010f5da76

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_special_frob_sum

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
theorem _root_.solution : FrobCong.{u, v} := by
  intro R _ l hl ι _ u w j β
  obtain ⟨r, h⟩ := special_frob_sum hl Finset.univ (fun a => u a ^ (l ^ j) * w a) β
  refine ⟨r, ?_⟩
  rw [← h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_pow, ← pow_mul, ← pow_add]
end Formalism.DworkPowerSeriesWeights
