-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.upper_left_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:03.313355+00:00
-- url     : https://prove2.me/submissions/7b476c66-4e66-4c64-951d-575e7b6f945c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_x_sl
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_upper_right_normal_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_wC_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_upper_sum_mul_inverse_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_coordinate_commute_raising
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_xA_ggi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_upper_sum_gamma_inv_comm

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
theorem _root_.solution (hP : P.OK)
    (hN : ∀ l ∈ Icc 1 (P.k - 1), star (SS P l) * SS P l = kap P fun π => ((Nrm P l π : ℝ) : ℂ))
    (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) (hx1 : ∀ π, xC P π (Y + 1) ≠ 0) :
    t11 P Y = qC P Y • (ggiA P * kap P fun π => (xC P π (Y + 1))⁻¹) + t22 P Y * mA P Y * lA P Y := by
  have hw : ggiA P * (kap P fun π => wC P π Y) = qC P Y • (ggiA P * kap P fun π => (xC P π (Y + 1))⁻¹) +
      ggiA P * kap P fun π => ∑ l ∈ Icc 1 (P.k - 1),
        xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹ := by
    rw [← mul_smul_comm, ← mul_add, ← kap_smul, ← kap_add]
    exact congrArg (fun F => ggiA P * kap P F) (funext fun π => wC_id P hP π Y (hx1 π))
  have ha : ggA P * xA P Y * m0A P Y *
      (ggiA P * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j) =
      ggA P * m0A P Y * ggiA P * weightedSumBis P Y := by
    rw [← x_sl P Y hx]
    simp only [mul_assoc]
    rw [← mul_assoc (xA P Y) (m0A P Y), coordinate_commute_raising, mul_assoc, ← mul_assoc (xA P Y) (ggiA P), xA_ggi, mul_assoc]
  have hb : S12 P Y *
      (ggiA P * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j) =
      ggiA P * (kap P fun π => ∑ l ∈ Icc 1 (P.k - 1),
        xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹) + ggiA P * S4 P Y := by
    rw [← mul_assoc, upper_sum_gamma_inv_comm, mul_assoc, upper_sum_mul_inverse_sum P hN Y hx, mul_add]
  rw [← upper_right_normal_form P Y hx]
  unfold t11 t12 lA
  rw [hw, add_mul, mul_add, mul_add, ha, hb]
  abel
end Formalism.FourierDecayAlt.P.Mx5
