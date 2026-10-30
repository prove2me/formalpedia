-- Prove2me | solution 1 for DerivativeChainContinuation.positive_aligned_affine_history_count
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:33:31.81874+00:00
-- url     : https://prove2.me/submissions/fc133b4a-8781-47ca-9167-ef5da4016aee

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_affine_greedy_iff
import Theorems.Thm_DerivativeChainContinuation_positive_aligned_greedy_history_count
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


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators















theorem affine_greedy_bijOn (n : ℕ) (a : Fin (n+1) → ℂ)
    (o c : ℂ) (hc : c≠0) :
    Set.BijOn (fun z : Fin (n+1) → ℂ => fun i => o+c*z i)
      {z : Fin (n+1) → ℂ | IsGreedyChain a z}
      {z : Fin (n+1) → ℂ | IsGreedyChain (fun i => o+c*a i) z} := by
  refine ⟨?_,?_,?_⟩
  · intro z hz
    exact (affine_greedy_iff a z o c hc).mpr hz
  · intro z hz w hw he
    funext i
    exact mul_left_cancel₀ hc (add_left_cancel (congrFun he i))
  · intro z hz
    refine ⟨fun i => (z i-o)/c,affine_greedy_inverse a z o c hc hz,?_⟩
    funext i
    exact affine_inverse_value o c (z i) hc


























end DerivativeChainContinuation

theorem solution (n : ℕ) (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q)
    (o c : ℂ) (hc : c≠0) :
    {z : Fin (n+1) → ℂ | IsGreedyChain (fun i => o+c*a i) z}.Finite ∧
      Set.ncard {z : Fin (n+1) → ℂ | IsGreedyChain (fun i => o+c*a i) z}=k := by
  obtain ⟨hfinite,hcount⟩ := positive_aligned_greedy_history_count n a k r Q hk hQ hQdegree hp
  have hbij := affine_greedy_bijOn n a o c hc
  exact ⟨hbij.finite_iff_finite.mp hfinite,hbij.ncard_eq.symm.trans hcount⟩
