-- Prove2me | solution 1 for Cslib.polynomiallyBounded_iff_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:58:20.920836+00:00
-- url     : https://prove2.me/submissions/96d12288-520a-4b65-8972-acbca4f3b6af

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Common
import Mathlib.Tactic.FunProp
import Definitions.Def_CSLib_PolynomialGrowth

open Filter Cslib
variable {f g : ℕ → ℕ}

theorem solution {f : ℕ → ℕ} :
    PolynomiallyBounded f ↔ ∃ c d : ℕ, ∀ n, f n ≤ c * (n + 1) ^ d := by
  constructor
  · simp_rw [PolynomiallyBounded, EventuallyLE, eventually_atTop]
    intro ⟨d, m, h⟩
    have ⟨c, hc⟩ := (Set.finite_Iio m).image f |>.exists_le
    use c + 1, d
    intro n
    obtain (hn | hn) := n.lt_or_ge m
    · grw [hc _ ⟨n, hn, rfl⟩, c.le_add_right 1, ← d.one_le_pow' n, mul_one]
    · grw [h n hn, n.le_add_right 1, ← Nat.le_add_left 1 c, one_mul]
  · rintro ⟨c, d, hf⟩
    refine ⟨d + 1, ?_⟩
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (c * 2 ^ d)] with n hn hc
    calc
      f n ≤ c * (n + 1) ^ d := hf n
      _ ≤ c * (2 * n) ^ d := by gcongr; lia
      _ = (c * 2 ^ d) * n ^ d := by rw [mul_pow, mul_assoc]
      _ ≤ n * n ^ d := Nat.mul_le_mul_right _ hc
      _ = n ^ (d + 1) := (pow_succ' n d).symm
