-- Prove2me | solution 1 for Formalism.L2.Th1.A.addition_neg_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:12:38.440322+00:00
-- url     : https://prove2.me/submissions/d520d307-ca5e-4b5b-ae3c-0b4e19951b4c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_XPowSuccDvdOfDerivative
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_iDen_mul_inv
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_C
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_X
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_apply
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_Plus_inv_cc
import Theorems.Thm_Formalism_L2_Th1_A_Plus_inv_subst
import Theorems.Thm_Formalism_L2_Th1_A_Plus_nS_cc
import Theorems.Thm_Formalism_L2_Th1_A_Plus_nS_subst
import Theorems.Thm_Formalism_L2_Th1_A_Plus_subHom_C
import Theorems.Thm_Formalism_L2_Th1_A_Plus_subHom_X
import Theorems.Thm_Formalism_L2_Th1_A_Plus_subHom_apply
import Theorems.Thm_Formalism_L2_Th1_A_Plus_tDen_mul_inv
import Theorems.Thm_Formalism_L2_Th1_A_Plus_xPlus_subst
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_iSerSpec
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
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Nn
namespace Formalism.L2.Th1.A
theorem _root_.solution : PlusNegY.{u} := by
  intro R _ W xP yP _
  have hI : ISerSpec.{u} := iSerSpec
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hi0, -, -, -, -, hy, -, -⟩ := hI R W
    have hv := Plus.inv_subst W xP hI
    have hn := Plus.nS_subst W xP yP hI
    have hxp := Plus.xPlus_subst W xP yP hI
    have hqr := CurveSer.iDen_mul_inv W
    have htv := Plus.tDen_mul_inv W xP
    rw [← Plus.subHom_apply _ hi0] at hv hn hxp hy ⊢
    have φX : Plus.subHom (iSer W) hi0 X = X * invOfUnit (iDen W) (-1) := Plus.subHom_X _ _
    rw [yPlus, map_sub, map_sub, map_sub, map_neg, map_mul, map_mul, map_mul, map_sub, map_mul,
      map_pow, map_pow, Plus.subHom_C, Plus.subHom_C, Plus.subHom_C, φX, hv, hn, hxp, hy]
    simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
    rw [yPlus]
    have hx' : xPlus W xP (W.toAffine.negY xP yP) = C xP
        + X * nS W xP (W.toAffine.negY xP yP) * invOfUnit (tDen W xP) 1 ^ 2 := rfl
    simp only [WeierstrassCurve.Affine.negY] at hx' ⊢
    rw [hx']
    simp only [map_sub, map_neg, map_mul]
    generalize nS W xP (-yP - W.a₁ * xP - W.a₃) = n'
    generalize invOfUnit (iDen W) (-1) = r at hqr
    generalize invOfUnit (tDen W xP) 1 = v at htv
    generalize iDen W = q at hqr
    rw [tDen] at htv
    linear_combination (yS W + C W.a₁ * X * xS W + C W.a₃ * X ^ 3 + C yP * X ^ 3) * n' * v ^ 3
        * ((q * r) ^ 5 + (q * r) ^ 4 + (q * r) ^ 3 + (q * r) ^ 2 + q * r + 1) * hqr
      + C W.a₁ * X * n' * v ^ 2 * htv
  · simp only [xPlus, tS, nS, WeierstrassCurve.Affine.negY, map_add, map_sub, map_neg, map_mul,
      map_pow, map_ofNat]
    ring
  · rw [xPlus, map_add, coeff_C, if_neg one_ne_zero, zero_add, mul_assoc, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, Plus.nS_cc, Plus.inv_cc]
    ring
end Formalism.L2.Th1.A
