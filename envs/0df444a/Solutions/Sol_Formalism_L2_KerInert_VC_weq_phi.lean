-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.weq_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:17:54.606355+00:00
-- url     : https://prove2.me/submissions/56dbbee7-4c40-423b-966e-73b2a76540cc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_KerInert_VC_weq_vc
import Theorems.Thm_Formalism_L2_KerInert_VC_hU_C
import Theorems.Thm_Formalism_L2_KerInert_VC_hv_C
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
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
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R)
namespace Formalism.L2.KerInert.VC
theorem _root_.solution : psi W C = phi W C ^ 3 + PowerSeries.C (C • W).a₁ * phi W C * psi W C
    + PowerSeries.C (C • W).a₂ * phi W C ^ 2 * psi W C + PowerSeries.C (C • W).a₃ * psi W C ^ 2
    + PowerSeries.C (C • W).a₄ * phi W C * psi W C ^ 2 + PowerSeries.C (C • W).a₆ * psi W C ^ 3 := by
  have hw := (CurveSer.wSer_fixed W).2
  have h := weq_vc (PowerSeries.C W.a₁) (PowerSeries.C W.a₂) (PowerSeries.C W.a₃) (PowerSeries.C W.a₄)
    (PowerSeries.C W.a₆) (PowerSeries.C (C.u : R)) (PowerSeries.C ((C.u⁻¹ : Rˣ) : R)) (PowerSeries.C C.r)
    (PowerSeries.C C.s) (PowerSeries.C C.t) X (wSer W) (vv W C) hw (hv_C W C) (hU_C C)
  simp only [phi, psi, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆,
    map_mul, map_add, map_sub, map_pow, map_ofNat]
  linear_combination h
end Formalism.L2.KerInert.VC
