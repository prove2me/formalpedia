-- Prove2me | solution 1 for DerivativeChainContinuation.positive_constant_affine_greedy_zero
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:14:59.472493+00:00
-- url     : https://prove2.me/submissions/73b4c9ef-5bec-43a2-a62e-7cc53bf08052

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_affine_pure_power_greedy_zero
import Theorems.Thm_DerivativeChainContinuation_positive_constant_source_pure_power
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


theorem solution (n : ℕ) (a z : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : Q.natDegree=0) (hp : fromRoots a=spokePoly k r Q)
    (o c : ℂ) (hc : c≠0) (hz : IsGreedyChain (fun i => o+c*a i) z) :
    (∀ i,z i=o) ∧ chainCost z=0 := by
  exact affine_pure_power_greedy_zero n a z
    (positive_constant_source_pure_power n a k r Q hk hQ hQdegree hp) o c hc hz
