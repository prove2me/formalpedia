-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.leading_coeff_t11
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:02.888248+00:00
-- url     : https://prove2.me/submissions/cc5f82f8-d384-49ba-aea5-50baf1ec92ee

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_const_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_mul_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_lead_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_lead_xA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_leading_coeff_S21
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_leading_term_upper_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_leading_coeff_S4
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_leading_coeff_l0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_leading_term_lowering_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_wq_deg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_lead_coef

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
theorem _root_.solution (hP : P.OK) : Lead (P.k + 1) (1 : A P) (t11 P) := by
  have hk := hP.k_pos
  have h1 : Lead (P.k + 1) (ggiA P * kap P fun _ => -((P.T : ℂ) * P.T'))
      (fun Y => ggiA P * kap P fun π => (wNum P π /ₘ coordinatePolynomial P π).eval Y) :=
    (lead_kap P (P.k + 1) (fun π => wNum P π /ₘ coordinatePolynomial P π) (fun _ => -((P.T : ℂ) * P.T'))
      (fun π => (wq_deg P hP π).1) (fun π => (wq_deg P hP π).2)).const_mul (ggiA P)
  have h2 : Lead (P.k + 1) (ggA P * 1 * -(zA P * ggiA P) * -(zbA P * ggiA P))
      (fun Y => ggA P * xA P Y * m0A P Y * l0A P Y) :=
    ((((lead_xA P).const_mul (ggA P)).mul (leading_term_lowering_constant P)).mul (leading_coeff_l0 P)).congr (by omega) rfl fun Y => rfl
  have h3 : Lead (P.k + 1) (0 : A P) (fun Y => ggA P * m0A P Y * ggiA P * weightedSumBis P Y) :=
    ((((leading_term_lowering_constant P).const_mul (ggA P)).mul_const (ggiA P)).mul (leading_coeff_S21 P P.k (by omega))).congr
      (by omega) (mul_zero _) fun Y => rfl
  have h4 : Lead (P.k + 1) (0 : A P) (fun Y => S12 P Y * l0A P Y) :=
    ((leading_term_upper_sum P P.k (by omega)).mul (leading_coeff_l0 P)).congr rfl (zero_mul _) fun Y => rfl
  have h5 : Lead (P.k + 1) (0 : A P) (fun Y => ggiA P * S4 P Y) :=
    ((leading_coeff_S4 P (P.k + 1) (by omega)).const_mul (ggiA P)).congr rfl (mul_zero _) fun Y => rfl
  refine ((((h1.add h2).add h3).add h4).add h5).congr rfl ?_ fun Y => rfl
  rw [add_zero, add_zero, add_zero, lead_coef]
end Formalism.FourierDecayAlt.P.Mx5
