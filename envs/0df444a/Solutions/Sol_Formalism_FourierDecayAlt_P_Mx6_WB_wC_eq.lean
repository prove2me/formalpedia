-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.wC_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:53.169033+00:00
-- url     : https://prove2.me/submissions/caac84fe-6036-42ef-a1ab-526d4ff50f40

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_good1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_weight_model_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_q_eval
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_good1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_x_eval_shift_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.WB
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx6.WB
theorem _root_.solution (P : Par) (hP : P.OK) (π : Ty P) (u : ℂ) (hu : Good P u) :
    wC P π u = qC P u / xC P π (u + 1) +
      ∑ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
  have e1 := (weight_model_identity P hP π).eval u
  have hx1 : ∏ i ∈ Icc 1 (P.k - 1), (u + (rc P π i + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun i hi => by rw [← add_assoc]; exact good1 hu π i hi)
  rw [q_eval] at e1
  rw [x_eval_shift_prod]
  show (wNum P π /ₘ coordinatePolynomial P π).eval u = _
  apply mul_right_cancel₀ hx1
  rw [e1, add_mul, div_mul_cancel₀ _ hx1, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [← Finset.mul_prod_erase (Icc 1 (P.k - 1)) (fun i => u + (rc P π i + 1)) hl]
  have a1 := good1 hu π l hl
  have a2 : u + (rc P π l + 1) = u + rc P π l + 1 := by ring
  have a3 : xEx P {l} π u = ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (u + rc P π j) := by
    unfold xEx rc
    rw [Finset.sdiff_singleton_eq_erase]
  have a4 : (rho P π l : ℂ) = rc P π l := rfl
  rw [a2, a3, a4]
  field_simp
end Formalism.FourierDecayAlt.P.Mx6.WB
