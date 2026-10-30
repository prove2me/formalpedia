-- Prove2me | solution 1 for DerivativeChainContinuation.collinear_greedy_exactly_two
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:12:07.434589+00:00
-- url     : https://prove2.me/submissions/17bdb8cc-ee38-46ef-8e58-f41928125ea8

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_GreedyStatement
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_affine_greedy_iff
import Theorems.Thm_DerivativeChainContinuation_real_greedy_exactly_two
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators







theorem affine_inverse_value (o c w : ℂ) (hc : c≠0) : o+c*((w-o)/c)=w := by
  field_simp
  ring



theorem affine_greedy_inverse {n : ℕ} (a z : Fin (n+1) → ℂ)
    (o c : ℂ) (hc : c≠0) (hz : IsGreedyChain (fun i => o+c*a i) z) :
    IsGreedyChain a (fun i => (z i-o)/c) := by
  apply (affine_greedy_iff a _ o c hc).mp
  have he : (fun i => o+c*((z i-o)/c))=z := funext (fun i => affine_inverse_value o c (z i) hc)
  rwa [he]














end DerivativeChainContinuation

theorem solution (n : ℕ) (hn : 1 ≤ n) (a : Fin (n+1) → ℝ)
    (hspan : orderedSource a 0<orderedSource a (Fin.last n))
    (o c : ℂ) (hc : c≠0) :
    ∃ zL zR : Fin (n+1) → ℂ,zL≠zR ∧
      ∀ z : Fin (n+1) → ℂ,IsGreedyChain (fun i => o+c*(a i : ℂ)) z ↔ z=zL ∨ z=zR := by
  obtain ⟨zL,zR,hneq,hclass⟩ := real_greedy_exactly_two n hn a hspan
  have hinj : Function.Injective (fun z : Fin (n+1) → ℂ => fun i => o+c*z i) := by
    intro x y he
    funext i
    have h := congrFun he i
    exact mul_left_cancel₀ hc (add_left_cancel h)
  refine ⟨fun i => o+c*zL i,fun i => o+c*zR i,fun h => hneq (hinj h),?_⟩
  intro z
  constructor
  · intro hz
    let v : Fin (n+1) → ℂ := fun i => (z i-o)/c
    have hv := affine_greedy_inverse (fun i => (a i : ℂ)) z o c hc hz
    have he : z=(fun i => o+c*v i) := by
      funext i
      exact (affine_inverse_value o c (z i) hc).symm
    rcases (hclass v).mp hv with hl | hr
    · left; rw [he,hl]
    · right; rw [he,hr]
  · rintro (rfl | rfl)
    · exact (affine_greedy_iff _ zL o c hc).mpr ((hclass zL).mpr (Or.inl rfl))
    · exact (affine_greedy_iff _ zR o c hc).mpr ((hclass zR).mpr (Or.inr rfl))
