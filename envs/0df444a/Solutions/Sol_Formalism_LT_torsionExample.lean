-- Prove2me | solution 1 for Formalism.LT.torsionExample
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:12.968272+00:00
-- url     : https://prove2.me/submissions/ea06320e-080a-4aaf-8938-a57c75ab1fc7

import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SolveExistsProof
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_TorsionNormIterProof
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LT
universe u v
namespace Formalism.LT
theorem _root_.solution : TorsionExample := by
  unfold TorsionExample IsLTPoly
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp
  · simp [Polynomial.coeff_X]
  · simp [Polynomial.coeff_X]
  · intro i h1 h2
    simp [Polynomial.coeff_X, Polynomial.coeff_X_pow, h2, Ne.symm h1]
  · norm_num
  · have h : ‖((2 : ℕ) : ℚ_[2])‖ < 1 := Padic.norm_p_lt_one
    simpa using h
  · norm_num
end Formalism.LT
