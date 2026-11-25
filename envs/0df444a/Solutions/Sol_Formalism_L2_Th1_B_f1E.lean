-- Prove2me | solution 1 for Formalism.L2.Th1.B.f1E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:54:38.39253+00:00
-- url     : https://prove2.me/submissions/448f5149-9020-4aa2-b954-ec2bbd82e0cd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_SimeqPadicIntegers
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassSeriesIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffEqZeroOfParallelogram
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Theorems.Thm_Formalism_L2_Th1_B_cobRules
import Theorems.Thm_Formalism_L2_Th1_B_phEDef
import Theorems.Thm_Formalism_L2_Th1_B_parE
import Theorems.Thm_Formalism_L2_Th1_B_cube

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
theorem _root_.solution : LogSigmaOnePullbackCocycle := by
  intro K _ _ _ A kap e1 s2 w l i F hw hF hi hk hI h2
  have h0 := (phEDef K s2 e1 kap w l hF.2.2.1).1
  obtain ⟨hdiv, hsw⟩ := cobRules K F l (phE s2 e1 kap w l) hF h0
  have hd := cube K F l i (phE s2 e1 kap w l) hF hi h2 (parE K A kap e1 s2 w l i F hw hF hi hk hI)
  exact ⟨hdiv, hsw, hd, by rw [hsw]; exact hd⟩
end Formalism.L2.Th1.B
