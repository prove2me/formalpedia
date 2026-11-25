-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.log_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:11.118865+00:00
-- url     : https://prove2.me/submissions/3fe907b8-9203-4298-a227-72f4052e632e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_KerInert_VC_phi_cc
import Theorems.Thm_Formalism_L2_KerInert_VC_D_phi
import Theorems.Thm_Formalism_L2_KerInert_VC_cc_subst0
import Theorems.Thm_P2M_Formalism_L2_KerInert_VC_derivative_C_mul__5469c3081b6c
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_D_apply
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_fw_mul_om
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_integSpec
import Theorems.Thm_Formalism_L2_Th1_A_logSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.KerInert Formalism.L2.KerInert.VC
open Formalism.L2.Th1.A
variable {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)
namespace Formalism.L2.KerInert.VC
theorem _root_.solution : (logSer (C • W)).subst (phi W C) = PowerSeries.C (C.u : K) * logSer W := by
  have hs : HasSubst (phi W C) := HasSubst.of_constantCoeff_zero' (phi_cc W C)
  have h1 : derivative K (phi W C) * fw W = PowerSeries.C (C.u : K) * (fw (C • W)).subst (phi W C) := by
    rw [← D_phi, CurveSer.D_apply, mul_comm]
  have h2 : (fw (C • W)).subst (phi W C) * (om (C • W)).subst (phi W C) = 1 := by
    rw [← subst_mul hs, CurveSer.fw_mul_om, ← coe_substAlgHom hs, map_one]
  have h3 := CurveSer.fw_mul_om W
  have hd : derivative K ((logSer (C • W)).subst (phi W C)) = PowerSeries.C (C.u : K) * om W := by
    rw [derivative_subst hs, (logSpec K (C • W)).2.2.1]
    linear_combination (-((om (C • W)).subst (phi W C) * derivative K (phi W C))) * h3
      + ((om (C • W)).subst (phi W C) * om W) * h1 + (PowerSeries.C (C.u : K) * om W) * h2
  have hc : constantCoeff ((logSer (C • W)).subst (phi W C)) = 0 :=
    cc_subst0 (phi_cc W C) (logSpec K (C • W)).1
  have hd2 : derivative K (PowerSeries.C (C.u : K) * logSer W) = PowerSeries.C (C.u : K) * om W := by
    rw [derivative_C_mul', (logSpec K W).2.2.1]
  have hc2 : constantCoeff (PowerSeries.C (C.u : K) * logSer W) = 0 := by
    simp [(logSpec K W).1]
  rw [(integSpec K _).2.2 _ hc hd, (integSpec K _).2.2 _ hc2 hd2]
end Formalism.L2.KerInert.VC
