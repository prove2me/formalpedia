-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.star_t11
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:24.565236+00:00
-- url     : https://prove2.me/submissions/6a3677e7-575a-4c96-9acb-19e511cb4ea7

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_ggi_gg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_gg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_ggi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_lowering_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_raising_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kappa_commute_l0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kappa_commute_raising_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_xA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_lower_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_upper_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_quartic_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_wC
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_ggi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_quartic_sum_gamma_inv_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_ggi_kap_gg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_conj_eq_of_nonneg_real

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
theorem _root_.solution (Y : ℂ) : star (t11 P Y) = t11 P (star Y) := by
  have e1 : star (ggiA P * kap P fun π => wC P π Y) = ggiA P * kap P fun π => wC P π (star Y) := by
    rw [star_mul, star_ggi, star_kap]
    simp only [star_wC]
    exact kap_ggi P _
  have e2 : star (ggA P * xA P Y * m0A P Y * l0A P Y) =
      ggA P * xA P (star Y) * m0A P (star Y) * l0A P (star Y) := by
    rw [star_mul, star_mul, star_mul, star_lowering_constant, star_raising_constant, star_xA, star_gg]
    exact conj_eq_of_nonneg_real (ggA P) (ggiA P) (xA P (star Y)) (m0A P (star Y)) (l0A P (star Y)) (ggi_gg P)
      (by unfold xA; exact ggi_kap_gg P _) (by unfold xA; exact kappa_commute_raising_constant P _ _) (by unfold xA; exact kappa_commute_l0 P _ _)
  have e3 : star (ggA P * m0A P Y * ggiA P * weightedSumBis P Y) = S12 P (star Y) * l0A P (star Y) := by
    rw [star_mul, star_mul, star_mul, star_lower_sum, star_ggi, star_raising_constant, star_gg]
    simp only [mul_assoc]
    rw [← mul_assoc (ggiA P) (ggA P), ggi_gg, one_mul, mul_one]
  have e4 : star (S12 P Y * l0A P Y) = ggA P * m0A P (star Y) * ggiA P * weightedSumBis P (star Y) := by
    rw [star_mul, star_lowering_constant, star_upper_sum]
  have e5 : star (ggiA P * S4 P Y) = ggiA P * S4 P (star Y) := by
    rw [star_mul, star_quartic_sum, star_ggi, quartic_sum_gamma_inv_comm]
  unfold t11
  rw [star_add, star_add, star_add, star_add, e1, e2, e3, e4, e5]
  abel
end Formalism.FourierDecayAlt.P.Mx5
