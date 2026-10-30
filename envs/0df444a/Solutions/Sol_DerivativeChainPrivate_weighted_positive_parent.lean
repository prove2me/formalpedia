-- Prove2me | solution 1 for DerivativeChainPrivate.weighted_positive_parent
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:58:28.200854+00:00
-- url     : https://prove2.me/submissions/152f9dc0-26b3-4673-9aad-f4e4ed932666

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
    (r k : ℕ) (y : ℝ) (hy : 0 < y)
    (hz : (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).eval y = 0) :
    ∃ x ∈ q.roots, y ≤ x := by
  classical
  by_contra h
  push Not at h
  have hqy : q.eval y ≠ 0 := by
    intro heq
    have hm := (Polynomial.mem_roots hq).mpr heq
    exact (not_lt_of_ge (le_refl y)) (h y hm)
  let s := (q.roots.map fun x => 1 / (y - x)).sum
  have hsnonneg : 0 ≤ s := by
    apply Multiset.sum_nonneg
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    exact le_of_lt (one_div_pos.mpr (sub_pos.mpr (h x hx)))
  have hd : q.derivative.eval y = q.eval y * s := hs.eval_derivative_eq_eval_mul_sum hqy
  simp only [eval_add, eval_mul, eval_C, eval_X] at hz
  rw [hd] at hz
  have heq : q.eval y * ((r + 1 : ℝ) + (k + 1 : ℝ) * y * s) = 0 := by
    nlinarith [hz]
  have hb := (mul_eq_zero.mp heq).resolve_left hqy
  have hprod : 0 ≤ (k + 1 : ℝ) * y * s :=
    mul_nonneg (mul_nonneg (by positivity) hy.le) hsnonneg
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  nlinarith
