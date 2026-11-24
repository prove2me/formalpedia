-- Prove2me | solution 1 for Formalism.L2.DIV.actionRational_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:16:49.304815+00:00
-- url     : https://prove2.me/submissions/f53131b1-913c-42da-821d-4b80ab18e2c8

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Theorems.Thm_Formalism_L2_DIV_fk_int_mem
import Theorems.Thm_Formalism_L2_DIV_fk_C_mem
import Theorems.Thm_Formalism_L2_DIV_fk_blockAct_mem
import Theorems.Thm_Formalism_L2_DIV_fk_det_mem
import Theorems.Thm_Formalism_L2_DIV_fk_descent
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_DIV_bVV_coe
import Theorems.Thm_Formalism_L2_DIV_bVVfun_int
import Theorems.Thm_Formalism_L2_DIV_detTw_eq
import Theorems.Thm_Formalism_L2_DIV_rhoK_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution : ActRat := by
  intro K _ ι _ n lam K0 g hg i j
  obtain ⟨Pj, hPj⟩ := bVVfun_int K lam j
  refine fk_descent K0 (bVVfun K lam) (bVVfun_spec K lam).1 (fun k => ?_)
    (fun k => (bVV K lam).repr (rhoK lam g (bVV K lam j)) k) ?_ i
  · obtain ⟨Pk, hPk⟩ := bVVfun_int K lam k
    rw [hPk]
    exact fk_int_mem K0 _
  · have h1 : ∑ k, (bVV K lam).repr (rhoK lam g (bVV K lam j)) k • bVVfun K lam k =
        actP lam g (bVVfun K lam j) := by
      have h := congrArg (fun x : VV K lam => (x : Pol K ι n)) ((bVV K lam).sum_repr (rhoK lam g (bVV K lam j)))
      simp only [rhoK_coe, bVV_coe, Submodule.coe_sum, Submodule.coe_smul] at h
      exact h
    rw [h1, hPj, actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul]
    refine mul_mem (fk_C_mem K0 ?_) (fk_blockAct_mem K0 _ (fun τ a b => hg τ b a) (fk_int_mem K0 _))
    rw [detTw_eq]
    exact prod_mem fun τ _ => zpow_mem (fk_det_mem K0 _ (hg τ)) _
end Formalism.L2.DIV
