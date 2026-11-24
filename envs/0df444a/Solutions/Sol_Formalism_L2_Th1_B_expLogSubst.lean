-- Prove2me | solution 1 for Formalism.L2.Th1.B.expLogSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:33:42.526094+00:00
-- url     : https://prove2.me/submissions/b539fff5-f4f0-4d92-9adc-f9026d014414

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RestrictSecondZeroInVarOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Theorems.Thm_Formalism_L2_Th1_B_Add0_subst_fExp
import Theorems.Thm_Formalism_L2_Th1_B_subst_fExp
import Theorems.Thm_Formalism_L2_Th1_B_subst_fLog


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
theorem _root_.solution : ExpLogSubst := by
  intro K _ _ ι κ _ φ hφ
  exact ⟨fun f hf => subst_fExp hφ hf, fun g hg => subst_fLog hφ hg⟩
end Formalism.L2.Th1.B
