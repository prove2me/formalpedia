-- Prove2me | solution 1 for DerivativeChainPrivate.derivative_positive_parent
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:53:44.560964+00:00
-- url     : https://prove2.me/submissions/2b9317cf-eb6a-4612-a116-683e91eababf

import Mathlib
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

open DerivativeChainPrivate
open Polynomial











theorem solution (q : Polynomial ℝ) (hq : q ≠ 0) (hs : q.Splits)
    (hdeg : 0 < q.natDegree) (y : ℝ) (hz : q.derivative.eval y = 0) :
    ∃ x ∈ q.roots, y ≤ x := by
  classical
  by_contra h
  push Not at h
  have hqy : q.eval y ≠ 0 := by
    intro heq
    exact (lt_irrefl y) (h y ((Polynomial.mem_roots hq).mpr heq))
  let s := (q.roots.map fun x => 1 / (y - x)).sum
  have hterms : ∀ a ∈ (q.roots.map fun x => 1 / (y - x)), 0 ≤ a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    exact (one_div_pos.mpr (sub_pos.mpr (h x hx))).le
  have hnonempty : q.roots ≠ 0 := by
    intro heq
    have hc := hs.natDegree_eq_card_roots
    simp only [heq, Multiset.card_zero] at hc
    omega
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hnonempty
  have hle : 1 / (y - x) ≤ s :=
    Multiset.single_le_sum hterms _ (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)
  have hd := hs.eval_derivative_eq_eval_mul_sum hqy
  rw [hz] at hd
  have hs0 : s = 0 := (mul_eq_zero.mp hd.symm).resolve_left hqy
  have hpos := one_div_pos.mpr (sub_pos.mpr (h x hx))
  linarith
