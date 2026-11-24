-- Prove2me | solution 1 for Formalism.L2.Th1.F.cm_theta_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:36:40.351016+00:00
-- url     : https://prove2.me/submissions/f0a8057e-48b6-42cc-87ea-fb649b6d0b9b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_sqrt_mul_selfC
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_conj_theta
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_theta_sq
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
namespace Cm1
private theorem four_mul_a_mul_c_complex_of_int (a : ℕ) (b c : ℤ) (d : ℕ) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    (4 : ℂ) * (a : ℂ) * (c : ℂ) = (b : ℂ) ^ 2 + (d : ℂ) := by
  have h' := congrArg (fun t : ℤ => (t : ℂ)) h
  push_cast at h'
  linear_combination h'
end Cm1
open Cm1
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Cm1
namespace Formalism.L2.Th1.F
theorem _root_.solution : CmThetaEq := by
  intro a b c d h
  have hs := Formalism.L2.Th1.F.Cm1.sqrt_mul_selfC d
  have hc := _root_.Formalism.L2.Th1.F.Cm1.four_mul_a_mul_c_complex_of_int a b c d h
  refine ⟨Formalism.L2.Th1.F.Cm1.theta_sq a b c d h, ?_, ?_⟩
  · rw [Formalism.L2.Th1.F.Cm1.conj_theta]; unfold cmTheta; ring
  · rw [Formalism.L2.Th1.F.Cm1.conj_theta]; unfold cmTheta
    linear_combination (-(1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2) * Complex.I_sq
      + (1 / 4 : ℂ) * hs - (1 / 4 : ℂ) * hc
end Formalism.L2.Th1.F
