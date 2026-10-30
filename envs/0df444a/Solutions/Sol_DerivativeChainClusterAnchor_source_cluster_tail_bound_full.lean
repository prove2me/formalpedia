-- Prove2me | solution 1 for DerivativeChainClusterAnchor.source_cluster_tail_bound_full
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:25:26.712338+00:00
-- url     : https://prove2.me/submissions/11a170d3-89d2-4d02-9a01-63ffe7504541

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterTail
import Theorems.Thm_DerivativeChainClusterAnchor_source_cluster_tail_bound
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
open scoped BigOperators
open DerivativeChainClusterAnchor

theorem solution {n r : ℕ} (a : Fin n → ℂ) (c : ℂ)
    (O : Finset (Fin n)) (hr : 0 < r) (hcut : 2*r < n) (hO : O.card ≤ r)
    (ε D : ℝ) (hε : 0 ≤ ε)
    (hnear : ∀ i, i ∉ O → ‖a i-c‖ ≤ ε) (hall : ∀ i, ‖a i-c‖ ≤ D) :
    (∑ m ∈ Finset.Icc (2*r+1) n, _root_.DerivativeChainClusterAnchor.anchorRadius a c m) ≤
      2*(n:ℝ)*ε+8*(r:ℝ)^((3:ℝ)/2)*Real.sqrt (D*ε/(n:ℝ)) := by
  have hn : 0 < n := by omega
  have hD : 0 ≤ D := (norm_nonneg (a ⟨0,hn⟩-c)).trans (hall ⟨0,hn⟩)
  by_cases hεD : ε ≤ D
  · exact _root_.DerivativeChainClusterAnchor.source_cluster_tail_bound a c O hr hcut hO ε D hε hεD hnear hall
  · have hDε : D ≤ ε := (lt_of_not_ge hεD).le
    have hsmall := _root_.DerivativeChainClusterAnchor.source_cluster_tail_bound a c O hr hcut hO D D hD le_rfl
      (fun i _ => hall i) hall
    refine hsmall.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left hDε (by positivity)
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hDε hD) (Nat.cast_nonneg n)
