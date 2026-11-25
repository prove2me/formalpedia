-- Prove2me | solution 1 for Formalism.L2.KerInert.VC.D_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:04:26.097014+00:00
-- url     : https://prove2.me/submissions/f7e8e0e8-9f2b-42a6-852b-53355baf9e2d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_L2_KerInert_VC_flow_vc
import Theorems.Thm_Formalism_L2_KerInert_VC_den_mul_vv
import Theorems.Thm_Formalism_L2_KerInert_VC_phi_cc
import Theorems.Thm_Formalism_L2_KerInert_VC_hU_C
import Theorems.Thm_Formalism_L2_KerInert_VC_hv_C
import Theorems.Thm_Formalism_L2_KerInert_VC_wSer_phi
import Theorems.Thm_Formalism_L2_KerInert_VC_D_C
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_C
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_X
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_apply
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_Plus_subHom_C
import Theorems.Thm_Formalism_L2_Th1_A_Plus_subHom_X
import Theorems.Thm_Formalism_L2_Th1_A_Plus_subHom_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_flowU
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
theorem _root_.solution : D W (phi W C) = PowerSeries.C (C.u : R) * (fw (C • W)).subst (phi W C) := by
  obtain ⟨-, -, hFl, hfwAt, hfuAt, -⟩ := flowU R W
  obtain ⟨-, hDX, hDw⟩ := hFl
  rw [hfwAt] at hDX
  rw [hfuAt] at hDw
  have hs : HasSubst (phi W C) := HasSubst.of_constantCoeff_zero' (phi_cc W C)
  have hfwsub : (fw (C • W)).subst (phi W C) = 1 - PowerSeries.C (C • W).a₁ * phi W C
      - PowerSeries.C (C • W).a₂ * phi W C ^ 2 - 2 * PowerSeries.C (C • W).a₃ * psi W C
      - 2 * PowerSeries.C (C • W).a₄ * phi W C * psi W C - 3 * PowerSeries.C (C • W).a₆ * psi W C ^ 2 := by
    rw [← ISer.subHom_apply _ (phi_cc W C)]
    simp only [fw, map_sub, map_mul, map_pow, map_one, map_ofNat, ISer.subHom_X, ISer.subHom_C]
    rw [ISer.subHom_apply, wSer_phi]
  have hvD : D W (vv W C) = -(vv W C) ^ 2 * D W (den W C) := by
    have h1 : D W (den W C * vv W C) = 0 := by rw [den_mul_vv, Derivation.map_one_eq_zero]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
    have h2 := den_mul_vv W C
    linear_combination (vv W C) * h1 - (D W (vv W C)) * h2
  have hdenD : D W (den W C) = PowerSeries.C C.s * D W X + PowerSeries.C (C.t - C.s * C.r) * D W (wSer W) := by
    simp only [den, map_add, Derivation.leibniz, smul_eq_mul, D_C, Derivation.map_one_eq_zero]
    ring
  have hphiD : D W (phi W C) = PowerSeries.C (C.u : R) * ((D W X - PowerSeries.C C.r * D W (wSer W)) * vv W C
      + (X - PowerSeries.C C.r * wSer W) * D W (vv W C)) := by
    simp only [phi, map_sub, Derivation.leibniz, smul_eq_mul, D_C]
    ring
  rw [hphiD, hvD, hdenD, hDX, hDw, hfwsub]
  have hw := (CurveSer.wSer_fixed W).2
  have h := flow_vc (PowerSeries.C W.a₁) (PowerSeries.C W.a₂) (PowerSeries.C W.a₃) (PowerSeries.C W.a₄)
    (PowerSeries.C W.a₆) (PowerSeries.C (C.u : R)) (PowerSeries.C ((C.u⁻¹ : Rˣ) : R)) (PowerSeries.C C.r)
    (PowerSeries.C C.s) (PowerSeries.C C.t) X (wSer W) (vv W C) hw (hv_C W C) (hU_C C)
  simp only [phi, psi, fw, fu, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆,
    map_mul, map_add, map_sub, map_pow, map_ofNat] at h ⊢
  linear_combination h
end Formalism.L2.KerInert.VC
