-- Prove2me | solution 1 for Formalism.L2.DIV.pairTransport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:16:00.571611+00:00
-- url     : https://prove2.me/submissions/549b76e5-33ac-4858-9bfc-301dbbc7fbc0

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_P2M_Formalism_L2_DIV_conjTranspose_transpose__09b67af54be3
import Theorems.Thm_Formalism_L2_DIV_fockL_blockAct_adj
import Theorems.Thm_Formalism_L2_DIV_pairP_apply
import Theorems.Thm_Formalism_L2_DIV_detTw_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution : PairTransport := by
  intro K _ _ ι _ n lam G g g' F F'
  have hs : gramTw lam (fun τ => (g τ : Matrix (Fin n) (Fin n) K)ᴴ * G τ * (g' τ : Matrix (Fin n) (Fin n) K)) =
      star (detTwK lam g) * gramTw lam G * detTwK lam g' := by
    rw [detTw_eq, detTw_eq, star_prod]
    unfold gramTw
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, mul_zpow, mul_zpow, star_zpow₀]
  have hb : Formalism.GradedWeylDivisibility.blockAct K (fun τ => (((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)ᴴ)
        (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) (trAct g' F')) =
      Formalism.GradedWeylDivisibility.blockAct K
        (fun τ => ((g τ : Matrix (Fin n) (Fin n) K)ᴴ * G τ * (g' τ : Matrix (Fin n) (Fin n) K))ᵀ) F' := by
    unfold trAct
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, blockAct_comp, blockAct_comp]
    congr 2
    funext τ
    rw [Matrix.transpose_mul, Matrix.transpose_mul, conjTranspose_transpose']
  rw [pairP_apply, pairP_apply, hs]
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, LinearMap.map_smulₛₗ, map_smul, smul_eq_mul,
    starRingEnd_apply]
  unfold trAct at hb ⊢
  rw [fockL_blockAct_adj, hb]
  ring
end Formalism.L2.DIV
