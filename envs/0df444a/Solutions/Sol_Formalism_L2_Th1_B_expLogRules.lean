-- Prove2me | solution 1 for Formalism.L2.Th1.B.expLogRules
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:49:43.009841+00:00
-- url     : https://prove2.me/submissions/80795401-ede1-4b2c-8a33-d04e47af5956

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RestrictSecondZeroInVarOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_fExp
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_fLog
import Theorems.Thm_Formalism_L2_Th1_B_fExp_add
import Theorems.Thm_Formalism_L2_Th1_B_fExp_fLog
import Theorems.Thm_Formalism_L2_Th1_B_fLog_fExp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
namespace Formalism.L2.Th1.B
theorem _root_.solution : ExpLogRules := by
  intro K _ _ ι
  exact ⟨fun f g hf hg => fExp_add hf hg, fun f hf => ⟨constantCoeff_fExp hf, fLog_fExp hf⟩,
    fun g hg => ⟨constantCoeff_fLog hg, fExp_fLog hg⟩⟩
end Formalism.L2.Th1.B
