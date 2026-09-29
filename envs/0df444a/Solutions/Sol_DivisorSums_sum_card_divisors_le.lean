-- Prove2me | solution 1 for DivisorSums.sum_card_divisors_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T18:09:49.797905+00:00
-- url     : https://prove2.me/submissions/faa316c2-02f1-43ec-8f08-34706eff0a8d

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.BV.DivisorSum =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# V1b — the divisor summatory bound (`Salt/BV/DivisorSum.lean`)

Design: `docs/blueprints/bv.md`, node `V1b`. A confirmed mathlib gap: the
classical divisor-summatory estimate

`∑_{n ∈ Icc 1 x} τ(n) ≤ x·(1 + log x)`

(`τ(n) = n.divisors.card`), plus the ℓ²-flavored corollary the Type II
Cauchy–Schwarz step wants, `∑_{n ≤ x} (log n)² ≤ x·(log x)²`.

Route for the first (shorter than the originally-scouted manual divisor
swap, thanks to an existing mathlib hyperbola-method identity):

1. `ArithmeticFunction.sigma_zero_apply : σ 0 n = n.divisors.card` identifies
   `τ` with the arithmetic function `σ 0`.
2. `ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div : ∑_{n ∈ Ioc 0 N} σ 0 n
   = ∑_{n ∈ Ioc 0 N} (N / n)` is EXACTLY the divisor-swap double-count
   `∑_n τ(n) = ∑_d ⌊x/d⌋` already landed in mathlib (the manual
   `Finset.sum_comm'`/`reindex_core` idiom from `Salt/LS/TypeSums.lean` and
   `Salt/LS/PhiSum.lean` is therefore NOT needed here — this identity is the
   pre-packaged form of that same swap).
3. `⌊x/n⌋ ≤ x/n` (`Nat.cast_div_le`), then the harmonic bound
   `∑_{n ∈ Icc 1 x} 1/n ≤ 1 + log x` (`harmonic_le_one_add_log`, converted
   from `harmonic`'s `Icc`-sum form via `harmonic_eq_sum_Icc`, mirroring the
   cast pattern in `Salt/LS/PhiSum.lean`'s `sum_inv_totient_le`).

The second theorem is termwise: for `n ∈ Icc 1 x`, `0 ≤ log n ≤ log x`
(monotonicity of `log` on `n ≥ 1`), so `(log n)² ≤ (log x)²`; sum over the
`x`-element index set.
-/

namespace Salt.BV

open Finset

/-- **V1b (divisor summatory).** `∑_{n ∈ Icc 1 x} τ(n) ≤ x·(1 + log x)`, via
the mathlib hyperbola-method identity `sum_Ioc_sigma0_eq_sum_div` (the
divisor swap `∑_n τ(n) = ∑_d ⌊x/d⌋`) followed by `⌊x/d⌋ ≤ x/d` and the
harmonic bound. -/
theorem sum_card_divisors_le (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) ≤ x * (1 + Real.log x) := by
  have hIcc : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  -- Step 1: identify `τ` with `σ 0` and apply the mathlib hyperbola identity.
  have hswap : ∑ n ∈ Finset.Icc 1 x, (n.divisors.card : ℕ)
      = ∑ n ∈ Finset.Icc 1 x, (x / n) := by
    rw [hIcc]
    simp only [← ArithmeticFunction.sigma_zero_apply]
    exact ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div x
  -- Step 2: cast to `ℝ` and bound `⌊x/n⌋ ≤ x/n` termwise, then apply harmonic.
  have hcast : ∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ))
      = ∑ n ∈ Finset.Icc 1 x, ((x / n : ℕ) : ℝ) := by
    have := congrArg (fun s : ℕ => (s : ℝ)) hswap
    simpa using this
  rw [hcast]
  have hstep : ∑ n ∈ Finset.Icc 1 x, ((x / n : ℕ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 x, (x : ℝ) / n := by
    apply Finset.sum_le_sum
    intro n _
    exact Nat.cast_div_le
  have hfac : ∑ n ∈ Finset.Icc 1 x, (x : ℝ) / n
      = (x : ℝ) * ∑ n ∈ Finset.Icc 1 x, (1 : ℝ) / n := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => by rw [mul_one_div])
  have hEq : ((harmonic x : ℚ) : ℝ) = ∑ n ∈ Finset.Icc 1 x, (1 : ℝ) / n := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl (fun n _ => by rw [one_div])
  have hharm : ∑ n ∈ Finset.Icc 1 x, (1 : ℝ) / n ≤ 1 + Real.log x := by
    rw [← hEq]
    exact harmonic_le_one_add_log x
  calc ∑ n ∈ Finset.Icc 1 x, ((x / n : ℕ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 x, (x : ℝ) / n := hstep
    _ = (x : ℝ) * ∑ n ∈ Finset.Icc 1 x, (1 : ℝ) / n := hfac
    _ ≤ (x : ℝ) * (1 + Real.log x) :=
        mul_le_mul_of_nonneg_left hharm (by positivity)

/-- **V1b corollary (ℓ²-flavored).** `∑_{n ∈ Icc 1 x} (log n)² ≤ x·(log x)²`,
termwise via monotonicity of `log` on `n ≥ 1`. -/
theorem sum_log_sq_le (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 x, (Real.log n) ^ 2 ≤ x * (Real.log x) ^ 2 := by
  have hcard : (Finset.Icc 1 x).card = x := by
    rw [Nat.card_Icc]; omega
  calc ∑ n ∈ Finset.Icc 1 x, (Real.log n) ^ 2
      ≤ ∑ _n ∈ Finset.Icc 1 x, (Real.log x) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_Icc] at hn
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
        have hnx : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hn.2
        have hlogn_nonneg : 0 ≤ Real.log n := Real.log_nonneg hn1
        have hlog_le : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) hnx
        exact pow_le_pow_left₀ hlogn_nonneg hlog_le 2
    _ = (x : ℝ) * (Real.log x) ^ 2 := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]

end Salt.BV

end




section
open Finset

theorem solution (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) ≤ x * (1 + Real.log x) := by
  apply Salt.BV.sum_card_divisors_le <;> assumption

end

