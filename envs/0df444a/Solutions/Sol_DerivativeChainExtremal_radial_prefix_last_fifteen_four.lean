-- Prove2me | solution 1 for DerivativeChainExtremal.radial_prefix_last_fifteen_four
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:14:40.306376+00:00
-- url     : https://prove2.me/submissions/116d3df2-1621-47fb-ba9f-69fa2e7467e4

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainExtremal_radial_prefix_centroid_four
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation



theorem solution (p : Polynomial ℂ)
    (n m k r : ℕ) (hdegree : p.natDegree=n+1) (q : Polynomial ℝ) (σ C₀ : ℂ)
    (hm : 1 ≤ m) (hmn : m ≤ n+1) (hk : 2 ≤ k) (hr : r < k)
    (hq : q.Splits) (hC : C₀ ≠ 0) (hσ : ‖σ‖=1)
    (hcore : (derivative^[n+1-m] p).comp (C (_root_.DerivativeChainContinuation.rootCentroid p)+C σ*X)=C C₀*_root_.DerivativeChainPrivate.spokePoly k r q)
    (ha : ∀ w : ℂ, p.eval w=0 → ‖w‖ ≤ 1) (hd : n+1-m ≤ 15) :
    ∃ z : Fin (n+1) → ℂ,
      (∀ i, (derivative^[n+1-(i.val+1)] p).eval (z i)=0) ∧ z 0=_root_.DerivativeChainContinuation.rootCentroid p ∧ _root_.DerivativeChainPrivate.chainCost z ≤ 4 := by
  apply _root_.DerivativeChainExtremal.radial_prefix_centroid_four p n m k r hdegree q σ C₀ hm hmn hk hr hq hC hσ hcore ha
  calc
    _ ≤ ((n+1-m+1:ℕ):ℝ)*1 := mul_le_mul_of_nonneg_left
      (by nlinarith [sq_nonneg ‖_root_.DerivativeChainContinuation.rootCentroid p‖]) (Nat.cast_nonneg _)
    _ ≤ 16 := by
      rw [mul_one]
      exact_mod_cast (show n+1-m+1 ≤ 16 by omega)
