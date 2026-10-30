-- Prove2me | solution 1 for DerivativeChainClusterAnchor.dominant_cluster_narrow
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T05:47:15.767601+00:00
-- url     : https://prove2.me/submissions/0dd2c14d-9bba-439e-9d5e-2d5b472c2d61

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainClusterAnchor_actual_polynomial_slots
import Theorems.Thm_DerivativeChainClusterAnchor_dominant_cluster_narrow_array
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






theorem solution (p : ℂ[X]) (hp : p.Monic) (n r : ℕ)
    (hdegree : p.natDegree=n) (hn : 16 ≤ n) (hr : 0 < r) (hcube : 4*r^3 ≤ n^2)
    (o c : ℂ) (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 ≤ ε) (hsmall : ε ≤ R/(512*(n:ℝ)))
    (hsource : ∀ z ∈ p.roots, ‖z-o‖ ≤ R) (hc : ‖c-o‖ ≤ R)
    (hcluster : (p.roots.filter (fun z => ε < ‖z-c‖)).card ≤ r) :
    ∃ z : Fin n → ℂ, (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ (7567/1920:ℝ)*R ∧ (0 < R → _root_.DerivativeChainPrivate.chainCost z < 4*R) := by
  classical
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨a,hpa,hmem,hcard⟩ := _root_.DerivativeChainClusterAnchor.actual_polynomial_slots p hp (n+1) hdegree (fun z => ε < ‖z-c‖)
    let O := (Finset.univ : Finset (Fin (n+1))).filter (fun i => ε < ‖a i-c‖)
    have hO : O.card ≤ r := hcard.le.trans hcluster
    have hnear (i : Fin (n+1)) (hi : i ∉ O) : ‖a i-c‖ ≤ ε := by simpa [O] using hi
    obtain ⟨z,hz,hcost,hstrict⟩ := _root_.DerivativeChainClusterAnchor.dominant_cluster_narrow_array n r a o c O R ε hn hr hcube hO hR hε
      (by simpa only [Nat.cast_add,Nat.cast_one] using hsmall) (fun i => hsource (a i) (hmem i)) hc hnear
    refine ⟨z,?_,hcost,hstrict⟩
    intro i
    rw [hpa]
    exact hz i
