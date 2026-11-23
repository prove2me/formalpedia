-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.mixed_relation_diagonal_four
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:42.813713+00:00
-- url     : https://prove2.me/submissions/7ab29ef3-8ff9-4ac0-91a9-8ba3601d6ebb

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_xC_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_coordinate_shift_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lc1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_gG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Gg__2bb78f
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_absSand
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_g__636104
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_relD4core

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution (hN : SSNorm) (hM : SSMixed) (hS : NabSS) (hK : Curvature) (hP : P.OK)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (t22 P v * mt P u * lA P v * t22 P u - t22 P v * lA P v * mt P u * t22 P u) =
      dA P v * t22 P u - t22 P v * dA P u := by
  have h := relD4core P hN hM hS hK hP u v hu hv
  have e : (u - v) • (t22 P v * mt P u * lA P v * t22 P u - t22 P v * lA P v * mt P u * t22 P u) =
      t22 P v * ((u - v) • (mt P u * lA P v - lA P v * mt P u)) * t22 P u := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
  rw [e, h, t22, t22, xA, xA, absSand _ _ _ _ _ (gG P) (Gg P) (kap_sc P _ _) (kap_sc P _ _) (kap_sc P _ _) (kap_sc P _ _)]
  have e3 : dA P v * (ggA P * kap P fun π => xC P π u) = kap P fun π => qC P v * (xC P π (v + 1))⁻¹ * xC P π u := by
    rw [dA, smul_mul_assoc, mul_assoc, lc (kap_g P _), lc1 (Gg P), kap_mul, ← map_smul]
    congr 1
    funext π
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]; ring
  have e4 : (ggA P * kap P fun π => xC P π v) * dA P u = kap P fun π => xC P π v * (qC P u * (xC P π (u + 1))⁻¹) := by
    rw [dA, mul_smul_comm, mul_assoc, lc (kap_G P _), lc1 (gG P), kap_mul, ← map_smul]
    congr 1
    funext π
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]; ring
  rw [e3, e4, kap_mul, kap_mul, ← map_sub]
  congr 1
  funext π
  have h1 := xC_ne P hu π
  have h2 := xC_ne P hv π
  have h3 := coordinate_shift_ne_zero P hu π
  have h4 := coordinate_shift_ne_zero P hv π
  simp only [Pi.mul_apply, Pi.sub_apply, hh]
  field_simp
end Formalism.FourierDecayAlt.P.Mx6
