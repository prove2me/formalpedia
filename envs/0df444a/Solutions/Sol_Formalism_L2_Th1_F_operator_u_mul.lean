-- Prove2me | solution 1 for Formalism.L2.Th1.F.operator_u_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:37:43.818171+00:00
-- url     : https://prove2.me/submissions/dd345335-feeb-43ee-b715-15ba2087a87f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_OperatorUComm
import Theorems.Thm_Formalism_L2_Th1_F_OperatorUThetaLemmas_herm_sub_herm
import Theorems.Thm_Formalism_L2_Th1_F_OperatorUThetaLemmas_herm_add_left
import Theorems.Thm_Formalism_L2_Th1_F_OperatorUThetaLemmas_herm_add_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.F
namespace OperatorUThetaLemmas
end OperatorUThetaLemmas
open OperatorUThetaLemmas
private theorem mul_exp_mul_exp_eq_exp_mul_of_add_eq (f a b c d : ℂ) (h : a + b = c + d) :
    f * Complex.exp a * Complex.exp b = Complex.exp c * (f * Complex.exp d) := by
  rw [mul_assoc, ← Complex.exp_add, h, Complex.exp_add]
  ring
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open OperatorUThetaLemmas
namespace Formalism.L2.Th1.F
theorem _root_.solution : OpUMul := by
  intro L x y F z
  simp only [opU]
  rw [add_assoc z x y]
  apply mul_exp_mul_exp_eq_exp_mul_of_add_eq
  simp only [Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_add_left, Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_add_right]
  linear_combination (-(Real.pi : ℂ) / 2) * Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_sub_herm L x y
end Formalism.L2.Th1.F
