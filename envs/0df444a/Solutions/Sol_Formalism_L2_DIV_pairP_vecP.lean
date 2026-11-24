-- Prove2me | solution 1 for Formalism.L2.DIV.pairP_vecP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:28:34.593628+00:00
-- url     : https://prove2.me/submissions/b17ca994-20ea-4a4c-8ca2-a1e754cff3cd

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_blockAct_X
import Theorems.Thm_Formalism_L2_DIV_pairP_apply
import Theorems.Thm_Formalism_L2_DIV_lamVec_detShift
import Theorems.Thm_Formalism_L2_DIV_extremal_lamVec
import Theorems.Thm_Formalism_L2_DIV_fockL_X_X
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_DIV_fockL_apply
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
variable {K : Type} [Field K]
variable [StarRing K]
namespace Formalism.L2.DIV
theorem _root_.solution (G : Unit → Matrix (Fin 2) (Fin 2) K) (v w : Fin 2 → K) :
    pairP (fun _ => lamVec) G (vecP v) (vecP w) = star v ⬝ᵥ (G () *ᵥ w) := by
  have h1 : gramTw (fun _ : Unit => lamVec) G = 1 := by simp [gramTw, lamVec_detShift]
  have h2 : extNorm K (fun _ : Unit => lamVec) = 1 := by
    simp only [extNorm, Finset.univ_unique, Finset.prod_singleton, extremal_lamVec]
    rw [← fockL_apply, fockL_X_X, if_pos rfl]
  rw [pairP_apply, h1, h2]
  simp only [vecP, blockAct_X, Fin.sum_univ_two, Matrix.transpose_apply,
    ← smul_eq_C_mul, map_add, map_smul, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, fockL_X_X,
    smul_add, smul_smul]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simp only [starRingEnd_apply]
  ring
end Formalism.L2.DIV
