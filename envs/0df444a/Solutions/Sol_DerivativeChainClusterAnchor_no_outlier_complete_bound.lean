-- Prove2me | solution 1 for DerivativeChainClusterAnchor.no_outlier_complete_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T04:05:49.33638+00:00
-- url     : https://prove2.me/submissions/82e5674e-7b11-4bf3-9536-c653e8f2dc08

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainClusterAnchor_all_roots_cluster_polynomial
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
set_option maxHeartbeats 1000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate
open DerivativeChainClusterAnchor

theorem solution (p : ℂ[X]) (hp : p.Monic) (n : ℕ)
    (hdegree : p.natDegree=n) (hn : 0 < n) (c : ℂ) (R ε : ℝ) (hR : 0 ≤ R)
    (hε : 0 ≤ ε) (hsmall : ε ≤ R/(16*(n:ℝ))) (hsource : ∀ z ∈ p.roots, ‖z-c‖ ≤ ε) :
    ∃ z : Fin n → ℂ, (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ R/16 ∧ (0 < R → _root_.DerivativeChainPrivate.chainCost z < 4*R) := by
  obtain ⟨z,hz,hcost⟩ := _root_.DerivativeChainClusterAnchor.all_roots_cluster_polynomial p hp n hdegree hn c ε hε hsource
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hpred : ((n-1:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hroot : Real.sqrt ((n-1:ℕ):ℝ) ≤ (n:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hnR)]
  have hmul := (le_div_iff₀ (by positivity : (0:ℝ) < 16*(n:ℝ))).mp hsmall
  have hbound : _root_.DerivativeChainPrivate.chainCost z ≤ R/16 := by
    have hc := hcost.trans (mul_le_mul_of_nonneg_right hroot hε)
    nlinarith
  exact ⟨z,hz,hbound,fun hpos => by nlinarith⟩
