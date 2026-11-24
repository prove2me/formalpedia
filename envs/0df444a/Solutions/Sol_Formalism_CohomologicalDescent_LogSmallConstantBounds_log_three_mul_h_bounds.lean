-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.log_three_mul_h_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:08.928804+00:00
-- url     : https://prove2.me/submissions/f8b1ab91-d66d-4512-8361-0021cd18f23f

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_b__eef42fd5826a
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsBasic_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_add_seven_le_h

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
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) :
    P.L ≤ Real.log (3 * P.h) ∧ Real.log (3 * P.h) ≤ P.L + Real.log 6 := by
  have hb := b_pos' P
  have hh : P.h ≤ 2 * P.b := (paramsBasic_holds P H G).2.2
  have hh2 := b_add_seven_le_h H
  constructor
  · rw [← log_b' P]
    exact Real.log_le_log hb (by linarith)
  · calc Real.log (3 * P.h) ≤ Real.log (6 * P.b) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 6 + P.L := by rw [Real.log_mul (by norm_num) hb.ne', log_b']
      _ = P.L + Real.log 6 := by ring
end Formalism.CohomologicalDescent.LogSmallConstantBounds
