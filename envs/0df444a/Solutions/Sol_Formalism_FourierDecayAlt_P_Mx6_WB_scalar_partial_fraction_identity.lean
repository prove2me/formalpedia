-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.scalar_partial_fraction_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:55.650795+00:00
-- url     : https://prove2.me/submissions/934e0039-dc9d-41e8-9a36-73d7e7b00847

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_good0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_good1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_quad
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_weighted_sum_difference_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_rc_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_weight_model_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_q_polynomial_monic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_natDegree_q1_polynomial
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_q_eval
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_model_root
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_s_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_good0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_good1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_coordinate_product_eq
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
theorem _root_.solution (P : Par) (hP : P.OK) (π : Ty P) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) * ((u + v + 1 + 2 * (aC P π : ℂ)) * (P.TT : ℂ) + ∑ j ∈ Icc 1 (P.k - 1),
      (((Nrm P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ) + 1) * (v + (rho P π j : ℂ) + 1)) -
        ((NrmDown P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ)) * (v + (rho P π j : ℂ))))) =
      qC P v / (xC P π v * xC P π (v + 1)) - qC P u / (xC P π u * xC P π (u + 1)) := by
  have hc : -((P.T : ℂ) * P.T') ≠ 0 := by
    have h1 : (P.T : ℂ) ≠ 0 := by exact_mod_cast hP.T_pos.ne'
    have h2 : (P.T' : ℂ) ≠ 0 := by exact_mod_cast hP.T'_pos.ne'
    exact neg_ne_zero.2 (mul_ne_zero h1 h2)
  obtain ⟨c0, hw⟩ := quad (rc_inj P hP π) (q_polynomial_monic P) (natDegree_q1_polynomial P hP) hc
    (fun l => ((NrmDown P l π : ℝ) : ℂ)) (weight_model_identity P hP π) (model_root P hP π)
  rw [s_eq P hP π] at hw
  have h := weighted_sum_difference_identity (fun l => ((NrmDown P l π : ℝ) : ℂ)) (weight_model_identity P hP π) _ _ c0 hw u v
    (good0 hu π) (good1 hu π) (good0 hv π) (good1 hv π)
  rw [q_eval, q_eval, ← coordinate_product_eq, ← coordinate_product_eq, ← x_eval_shift_prod, ← x_eval_shift_prod] at h
  rw [← h]
  have hT : (P.TT : ℂ) = (P.T : ℂ) * P.T' := by unfold Par.TT; push_cast; ring
  rw [hT]
  have : ∀ j, (rho P π j : ℂ) = rc P π j := fun _ => rfl
  simp only [this]
  ring
end Formalism.FourierDecayAlt.P.Mx6.WB
