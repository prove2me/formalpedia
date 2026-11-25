-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.log_lJ_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:23.725254+00:00
-- url     : https://prove2.me/submissions/cda3dfff-0a85-4e56-b9bd-ce96cf9b89b5

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_b__eef42fd5826a
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsLog_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_eight_lt_lJ

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
    2 < Real.log P.lJ ∧ Real.log P.lJ ≤ P.L := by
  have h8 := eight_lt_lJ H G
  have hLJb := (paramsLog_holds P H G).2.2
  constructor
  · have he : Real.exp 2 < 8 := by
      have h := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [e]
      norm_num at h
      nlinarith [Real.exp_pos 1]
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ < Real.log P.lJ := Real.log_lt_log (Real.exp_pos 2) (by linarith)
  · calc Real.log P.lJ ≤ Real.log P.b := Real.log_le_log (by linarith) hLJb
      _ = P.L := log_b' P
end Formalism.CohomologicalDescent.LogSmallConstantBounds
