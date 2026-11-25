-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:27:45.709923+00:00
-- url     : https://prove2.me/submissions/6a554101-e413-4316-be82-fc1b743baaa0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_KerInert_VC_phi_cc
import Theorems.Thm_Formalism_L2_KerInert_VC_cc_subst0
import Theorems.Thm_P2M_Formalism_L2_KerInert_VC_subst_C__f714b10ebe9d
import Theorems.Thm_Formalism_L2_KerInert_VC_log_phi
import Theorems.Thm_Formalism_L2_KerInert_VC_cUi_cc
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_compInvSpec
import Theorems.Thm_Formalism_L2_Th1_A_expSpec
import Theorems.Thm_Formalism_L2_Th1_A_logSpec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.KerInert Formalism.L2.KerInert.VC
open Formalism.L2.Th1.A
variable {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)
namespace Formalism.L2.KerInert.VC
theorem _root_.solution : expSer (C • W) =
    (phi W C).subst ((expSer W).subst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X)) := by
  have hm0 := cUi_cc C
  have hmS : HasSubst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X) := HasSubst.of_constantCoeff_zero' hm0
  have he := expSpec K W
  have heS : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' he.1
  have hh0 : constantCoeff ((expSer W).subst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X)) = 0 := cc_subst0 hm0 he.1
  have hhS := HasSubst.of_constantCoeff_zero' hh0
  have hs : HasSubst (phi W C) := HasSubst.of_constantCoeff_zero' (phi_cc W C)
  have hlog : (logSer (C • W)).subst ((phi W C).subst ((expSer W).subst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X))) = X := by
    rw [← subst_comp_subst_apply hs hhS, log_phi, subst_mul hhS, subst_C' hh0,
      ← subst_comp_subst_apply heS hmS, he.2.2.1, subst_X hmS, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  have hl := logSpec K (C • W)
  have hsp := compInvSpec K (logSer (C • W)) hl.1 (by rw [hl.2.1]; exact isUnit_one)
  exact (hsp.2.2.2.2.1 _ (cc_subst0 hh0 (phi_cc W C)) hlog).symm
end Formalism.L2.KerInert.VC
