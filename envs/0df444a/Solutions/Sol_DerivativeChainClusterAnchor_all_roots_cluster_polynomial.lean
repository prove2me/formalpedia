-- Prove2me | solution 1 for DerivativeChainClusterAnchor.all_roots_cluster_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T04:00:19.460219+00:00
-- url     : https://prove2.me/submissions/62890640-2960-4005-849b-9fea0919b5b0

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainClusterAnchor_actual_polynomial_slots
import Theorems.Thm_DerivativeChainClusterAnchor_baseline_complete_chain_radius
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainClusterAnchor










theorem solution (p : ℂ[X]) (hp : p.Monic) (n : ℕ)
    (hdegree : p.natDegree=n) (hn : 0 < n) (c : ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hsource : ∀ z ∈ p.roots, ‖z-c‖ ≤ ε) :
    ∃ z : Fin n → ℂ, (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ Real.sqrt ((n-1:ℕ):ℝ)*ε := by
  classical
  obtain ⟨a,hpa,hmem,_⟩ := _root_.DerivativeChainClusterAnchor.actual_polynomial_slots p hp n hdegree (fun _ => True)
  obtain ⟨z,hz,hcost⟩ := _root_.DerivativeChainClusterAnchor.baseline_complete_chain_radius hn a c ε hε (fun i => hsource (a i) (hmem i))
  refine ⟨z,?_,hcost⟩
  intro i
  rw [hpa]
  exact hz i
