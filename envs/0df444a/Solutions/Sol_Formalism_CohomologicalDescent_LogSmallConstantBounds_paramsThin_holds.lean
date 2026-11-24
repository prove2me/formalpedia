-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.paramsThin_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:13.471278+00:00
-- url     : https://prove2.me/submissions/87d6e19f-50f5-499d-a501-bbd2598d2ba2

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_kmax_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : Elem_f := by
  intro P H G
  have nb := natBounds H
  have hw := G.w_gt
  have hk := kmax_le H G
  have e2 : 2 * P.b / P.lstar = 2 * (P.b / P.lstar) := by ring
  refine ⟨by linarith, ?_⟩
  unfold Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.w''
  exact div_le_self H.b'_pos.le (by nlinarith [H.x_ge, nb.n1])
end Formalism.CohomologicalDescent.LogSmallConstantBounds
