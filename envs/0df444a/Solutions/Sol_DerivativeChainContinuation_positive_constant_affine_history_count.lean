-- Prove2me | solution 1 for DerivativeChainContinuation.positive_constant_affine_history_count
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:36:19.874078+00:00
-- url     : https://prove2.me/submissions/9e43909b-20a2-4f51-8033-533abd822778

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_affine_pure_power_unique_history
import Theorems.Thm_DerivativeChainContinuation_positive_constant_source_pure_power
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


theorem solution (n : ℕ) (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : Q.natDegree=0) (hp : fromRoots a=spokePoly k r Q)
    (o c : ℂ) (hc : c≠0) :
    {z : Fin (n+1) → ℂ | IsGreedyChain (fun i => o+c*a i) z}.Finite ∧
      Set.ncard {z : Fin (n+1) → ℂ | IsGreedyChain (fun i => o+c*a i) z}=1 := by
  have hpower := positive_constant_source_pure_power n a k r Q hk hQ hQdegree hp
  have hset := (affine_pure_power_unique_history n a hpower o c hc).1
  rw [hset]
  exact ⟨Set.finite_singleton _,Set.ncard_singleton _⟩
