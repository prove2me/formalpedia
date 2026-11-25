-- Prove2me | solution 1 for Formalism.L2.Th1.A.weierstrass_p_prime_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:59:36.829998+00:00
-- url     : https://prove2.me/submissions/999ac0c8-d15f-42d1-b957-377b183fdddd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_eq
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wU_mul_xS
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_C_neg_two
import Theorems.Thm_Formalism_L2_Th1_A_Wp_sig_X
import Theorems.Thm_Formalism_L2_Th1_A_Wp_sig_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_dL_uPow
import Theorems.Thm_Formalism_L2_Th1_A_expSpec
import Theorems.Thm_Formalism_L2_Th1_A_toL_injective
import Theorems.Thm_Formalism_L2_Th1_A_wpShape
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
open More
namespace Formalism.L2.Th1.A
theorem _root_.solution : WpPrimeShape.{u} := by
  intro K _ _ W
  obtain ⟨e0, e1, -⟩ := expSpec K W
  have he : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' e0
  have hne : toL (expSer W) ≠ 0 := by
    intro h
    have h0 : expSer W = 0 := toL_injective (by rw [h, map_zero])
    rw [h0] at e1
    simp at e1
  constructor
  · rw [(wpShape K W).1, map_add, dL_uPow, dL_toL, WpSh.C_neg_two]
    norm_num
  · have h2 : (toL (expSer W))⁻¹ * toL (expSer W) = 1 := inv_mul_cancel₀ hne
    have h3 : Wp.sig he (wU W) * Wp.sig he (xS W) = 1 := by
      rw [← map_mul, CurveSer.wU_mul_xS, map_one]
    rw [yZ, ← Wp.sig_apply he, ← Wp.sig_apply he, CurveSer.wSer_eq, yS, map_mul, map_pow, map_neg,
      Wp.sig_X]
    linear_combination (-(Wp.sig he (wU W) * Wp.sig he (xS W)) *
      (((toL (expSer W))⁻¹ * toL (expSer W)) ^ 2 + (toL (expSer W))⁻¹ * toL (expSer W) + 1)) * h2
      - h3
end Formalism.L2.Th1.A
