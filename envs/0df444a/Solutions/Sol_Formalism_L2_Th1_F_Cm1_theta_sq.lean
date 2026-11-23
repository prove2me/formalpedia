-- Prove2me | solution 1 for Formalism.L2.Th1.F.Cm1.theta_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:37.321802+00:00
-- url     : https://prove2.me/submissions/4f23f325-46b6-4fda-9642-287811aa0c69

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_sqrt_mul_selfC
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
open Formalism.L2.Th1.F.Cm1
namespace Formalism.L2.Th1.F.Cm1
theorem _root_.solution (a : ℕ) (b c : ℤ) (d : ℕ) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    cmTheta b d ^ 2 = (b : ℂ) * cmTheta b d - (a : ℂ) * (c : ℂ) := by
  have hs := sqrt_mul_selfC d
  have hc := four_mul_a_mul_c_complex_of_int a b c d h
  unfold Formalism.L2.Th1.F.cmTheta
  linear_combination ((1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2) * Complex.I_sq
    - (1 / 4 : ℂ) * hs + (1 / 4 : ℂ) * hc
end Formalism.L2.Th1.F.Cm1
