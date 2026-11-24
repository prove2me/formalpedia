-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Pstep_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:22:01.338733+00:00
-- url     : https://prove2.me/submissions/eac396d0-5b35-4d43-9b6d-9c154735a2aa

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GlRel_sw
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_comm_S
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_diag_comm_omega
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Pstep_comm
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Pstep_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_vanish
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_E_Pstep_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_lower_kill

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
variable {E : ι → ι → Module.End K W}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution [CharZero K] (h : GlRel E) {NN : Submodule K W} (hN : ∀ a b, ∀ x ∈ NN, E a b x ∈ NN) {l : ℕ}
    (hev : ∀ (z : ι) (k : ℤ), ∀ x ∈ NN, E z z x = (k : K) • x → (l : ℤ) < |k| → x = 0)
    {S : Finset ι} {z : ι} (hz : z ∉ S) {u : W} (hu : u ∈ NN)
    (hS : ∀ a ∈ S, ∀ b ∈ S, E a b u = 0) (hzz : E z z u = 0) :
    ∀ a ∈ insert z S, ∀ b ∈ insert z S, E a b (Pstep E S z l u) = 0 := by
  have hP : Pstep E S z l u ∈ NN := Pstep_mem hN S z l u hu
  have hSS : ∀ a ∈ S, ∀ b ∈ S, E a b (Pstep E S z l u) = 0 := by
    intro a ha b hb
    have e1 := DFunLike.congr_fun (Pstep_comm S z l (E a b) (fun q => Om_comm_S h hz ha hb q)) u
    simp only [Module.End.mul_apply, hS a ha b hb, map_zero] at e1
    exact e1
  have hZ : E z z (Pstep E S z l u) = 0 := by
    have e1 := DFunLike.congr_fun (Pstep_comm S z l (E z z) (fun q => diag_comm_omega h hz q)) u
    simp only [Module.End.mul_apply, hzz, map_zero] at e1
    exact e1
  have hJ : ∀ j ∈ S, E j z (Pstep E S z l u) = 0 := by
    intro j hj
    have hjz : j ≠ z := fun e => hz (e ▸ hj)
    have hw : E z z (E j z u) = -((1 : ℕ) : K) • E j z u := by
      have e1 := DFunLike.congr_fun (h.sw z z j z) u
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
        if_neg (show ¬ z = j from fun e => hjz e.symm), if_pos (rfl : z = z), ↓reduceIte, LinearMap.zero_apply,
        zero_sub, LinearMap.neg_apply, hzz, map_zero, zero_add] at e1
      rw [e1, Nat.cast_one, neg_one_smul]
    rw [E_Pstep_apply h hz hj hS hzz l,
      Om_vanish h hN hev hz l 1 (E j z u) (hN _ _ _ hu) hw (by omega), smul_zero]
  have hne : ∀ b ∈ S, b ≠ z := fun b hb e => hz (e ▸ hb)
  intro a ha b hb
  rw [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact hZ
  · exact lower_kill h hN hev (hne b hb) hP (hJ b hb) (hSS b hb b hb) hZ
  · exact hJ a ha
  · exact hSS a ha b hb
end Formalism.InvariantFactorPaths.PW
