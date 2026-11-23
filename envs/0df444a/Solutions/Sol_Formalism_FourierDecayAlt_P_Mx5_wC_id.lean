-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.wC_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:06.124013+00:00
-- url     : https://prove2.me/submissions/2ffb26ce-cf34-40b7-a07f-8532b41de086

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_xC_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_fac_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_eval_x_polynomial
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_eval_wNum
import Theorems.Thm_Formalism_FourierDecayAlt_P_weight_exact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution (hP : P.OK) (π : Ty P) (Y : ℂ) (h1 : xC P π (Y + 1) ≠ 0) :
    wC P π Y = qC P Y * (xC P π (Y + 1))⁻¹ +
      ∑ l ∈ Icc 1 (P.k - 1), xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹ := by
  have hW : (wNum P π).eval Y = xC P π (Y + 1) * wC P π Y := by
    have h := congrArg (eval Y) (weight_exact P hP π)
    rw [eval_mul, eval_x_polynomial] at h
    exact h
  apply mul_left_cancel₀ h1
  rw [← hW, eval_wNum, mul_add, mul_sum]
  congr 1
  · rw [mul_comm (qC P Y), ← mul_assoc, mul_inv_cancel₀ h1, one_mul]
  · refine sum_congr rfl fun l hl => ?_
    have hne : Y + 1 + (rho P π l : ℂ) ≠ 0 := fac_ne P h1 hl
    have e : Y + (rho P π l : ℂ) + 1 = Y + 1 + (rho P π l : ℂ) := by ring
    rw [xC_split P l hl π (Y + 1), e]
    calc ((Nrm P l π : ℝ) : ℂ) * (xEx P {l} π Y * xEx P {l} π (Y + 1))
        = ((Y + 1 + (rho P π l : ℂ)) * (Y + 1 + (rho P π l : ℂ))⁻¹) *
          (((Nrm P l π : ℝ) : ℂ) * (xEx P {l} π Y * xEx P {l} π (Y + 1))) := by
          rw [mul_inv_cancel₀ hne, one_mul]
      _ = _ := by ring
end Formalism.FourierDecayAlt.P.Mx5
