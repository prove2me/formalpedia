-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.mulBy_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:00:18.376417+00:00
-- url     : https://prove2.me/submissions/9d7a128d-efd1-4e68-b728-b20717c01b44

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_KerInert_VC_phi_cc
import Theorems.Thm_Formalism_L2_KerInert_VC_phi_coeff_one
import Theorems.Thm_Formalism_L2_KerInert_VC_cc_subst0
import Theorems.Thm_P2M_Formalism_L2_KerInert_VC_subst_C__f714b10ebe9d
import Theorems.Thm_Formalism_L2_KerInert_VC_log_phi
import Theorems.Thm_Formalism_L2_KerInert_VC_cUi_cc
import Theorems.Thm_Formalism_L2_KerInert_VC_exp_eq
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_compInvSpec
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_expSpec
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
theorem _root_.solution (c : K) : Formalism.L2.Th1.C.mulBy (logSer (C • W)) (expSer (C • W)) c =
    (phi W C).subst ((Formalism.L2.Th1.C.mulBy (logSer W) (expSer W) c).subst (compInv (phi W C))) := by
  have hs : HasSubst (phi W C) := HasSubst.of_constantCoeff_zero' (phi_cc W C)
  have hci := compInvSpec K (phi W C) (phi_cc W C) (by rw [phi_coeff_one]; exact Units.isUnit _)
  have hp0 : constantCoeff (compInv (phi W C)) = 0 := hci.1
  have hpS : HasSubst (compInv (phi W C)) := HasSubst.of_constantCoeff_zero' hp0
  have hl := logSpec K W
  have he := expSpec K W
  have heS : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' he.1
  have hl' : logSer (C • W) = PowerSeries.C (C.u : K) * (logSer W).subst (compInv (phi W C)) := by
    have h := congrArg (fun f : K⟦X⟧ => f.subst (compInv (phi W C))) (log_phi W C)
    rw [subst_comp_subst_apply hs hpS, hci.2.1, X_subst, subst_mul hpS, subst_C' hp0] at h
    exact h
  have hq0 : constantCoeff (PowerSeries.C c * logSer (C • W)) = 0 := by
    simp [(logSpec K (C • W)).1]
  have hqS : HasSubst (PowerSeries.C c * logSer (C • W)) := HasSubst.of_constantCoeff_zero' hq0
  have hm0 := cUi_cc C
  have hmS : HasSubst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X) := HasSubst.of_constantCoeff_zero' hm0
  have hh0 : constantCoeff ((expSer W).subst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X)) = 0 := cc_subst0 hm0 he.1
  have hhS := HasSubst.of_constantCoeff_zero' hh0
  have hr0 : constantCoeff (PowerSeries.C c * logSer W) = 0 := by simp [hl.1]
  have hrS : HasSubst (PowerSeries.C c * logSer W) := HasSubst.of_constantCoeff_zero' hr0
  unfold Formalism.L2.Th1.C.mulBy
  rw [exp_eq, subst_comp_subst_apply hhS hqS, subst_comp_subst_apply hmS hqS, subst_mul hqS, subst_C' hq0,
    subst_X hqS, subst_comp_subst_apply hrS hpS, subst_mul hpS, subst_C' hp0, hl']
  congr 2
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm (((C.u⁻¹ : Kˣ) : K)) c, mul_assoc c,
    Units.inv_mul, mul_one]
end Formalism.L2.KerInert.VC
