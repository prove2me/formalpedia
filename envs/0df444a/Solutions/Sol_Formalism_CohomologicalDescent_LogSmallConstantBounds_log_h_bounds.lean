-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.log_h_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:11.073631+00:00
-- url     : https://prove2.me/submissions/38c64579-f8a2-4741-9fd7-07d7623833cc

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
section
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
private theorem log_two_le_seven_tenths : Real.log 2 ≤ 7 / 10 := by
  have h := Real.log_two_lt_d9
  have d : (0.6931471808 : ℝ) = 6931471808 / 10000000000 := by norm_num
  rw [d] at h
  linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) :
    0 < Real.log P.h ∧ Real.log P.h ≤ P.L + 0.7 := by
  have hb := b_pos' P
  have hh := (paramsBasic_holds P H G).2.2
  have h7 := b_add_seven_le_h H
  have h2 := log_two_le_seven_tenths
  constructor
  · exact Real.log_pos (by linarith)
  · have : Real.log P.h ≤ P.L + 7 / 10 := by
      calc Real.log P.h ≤ Real.log (2 * P.b) := Real.log_le_log (by linarith) hh
        _ = Real.log 2 + P.L := by rw [Real.log_mul (by norm_num) hb.ne', log_b']
        _ ≤ P.L + 7 / 10 := by linarith
    have d : (0.7 : ℝ) = 7 / 10 := by norm_num
    rw [d]
    exact this
end Formalism.CohomologicalDescent.LogSmallConstantBounds
