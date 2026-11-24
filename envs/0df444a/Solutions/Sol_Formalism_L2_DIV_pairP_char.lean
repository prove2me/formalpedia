-- Prove2me | solution 1 for Formalism.L2.DIV.pairP_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:56:18.178362+00:00
-- url     : https://prove2.me/submissions/e53b4187-f4ef-4a1d-a28b-d0a57af37bf4

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_fockL_C_left
import Theorems.Thm_Formalism_L2_DIV_pairP_apply
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
theorem _root_.solution (e : ℤ) (G : Unit → Matrix (Fin 1) (Fin 1) K) :
    pairP (fun _ => lamChar e) G (1 : Pol K Unit 1) 1 = G () 0 0 ^ e := by
  have h0 : (lamChar e).natW = fun _ => 0 := by
    funext i
    simp [DomWeight.natW, DomWeight.detShift, lamChar]
  have h2 : extNorm K (fun _ : Unit => lamChar e) = 1 := by
    simp only [extNorm, Finset.univ_unique, Finset.prod_singleton, extremal, Formalism.GradedWeylDivisibility.hw, h0]
    simp only [Formalism.GradedWeylDivisibility.nuNext]
    simp only [Nat.sub_self, dite_eq_ite, ite_self, pow_zero]
    rw [← fockL_apply, ← C_1, fockL_C_left]
    simp
  have hb : Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) (1 : Pol K Unit 1) = 1 := map_one _
  rw [pairP_apply, h2, hb, ← C_1, fockL_C_left]
  simp [gramTw, lamChar, DomWeight.detShift]
end Formalism.L2.DIV
