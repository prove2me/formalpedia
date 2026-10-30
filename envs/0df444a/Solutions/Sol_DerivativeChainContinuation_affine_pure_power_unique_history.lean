-- Prove2me | solution 1 for DerivativeChainContinuation.affine_pure_power_unique_history
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:17:14.111994+00:00
-- url     : https://prove2.me/submissions/ee265d20-9196-4e23-ab33-98f18638803a

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_actual_greedy_chain_exists
import Theorems.Thm_DerivativeChainContinuation_affine_pure_power_greedy_zero
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


theorem solution (n : ℕ) (a : Fin (n+1) → ℂ)
    (hp : fromRoots a=X^(n+1)) (o c : ℂ) (hc : c≠0) :
    {z : Fin (n+1) → ℂ | IsGreedyChain (fun i => o+c*a i) z}={fun _ => o} ∧
      (∃! z : Fin (n+1) → ℂ,IsGreedyChain (fun i => o+c*a i) z) := by
  obtain ⟨z,hz⟩ := actual_greedy_chain_exists n (fun i => o+c*a i)
  have hzconst : z=(fun _ => o) := funext (affine_pure_power_greedy_zero n a z hp o c hc hz).1
  have hcenter : IsGreedyChain (fun i => o+c*a i) (fun _ => o) := by rwa [hzconst] at hz
  have hset : {w : Fin (n+1) → ℂ | IsGreedyChain (fun i => o+c*a i) w}={fun _ => o} := by
    ext w
    simp only [Set.mem_ofPred_eq,Set.mem_singleton_iff]
    constructor
    · intro hw
      exact funext (affine_pure_power_greedy_zero n a w hp o c hc hw).1
    · rintro rfl
      exact hcenter
  refine ⟨hset,fun _ => o,hcenter,?_⟩
  intro w hw
  exact funext (affine_pure_power_greedy_zero n a w hp o c hc hw).1
