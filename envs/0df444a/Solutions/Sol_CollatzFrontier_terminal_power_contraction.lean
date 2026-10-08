-- Prove2me | solution 1 for CollatzFrontier.terminal_power_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-04T17:26:50.21098+00:00
-- url     : https://prove2.me/submissions/ca7d40f9-b074-4960-8e5c-5702b3139db0

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-
Self-contained solution. Pure ℕ arithmetic; no project definition is needed.
Helper lemma inlined (renamed under `CollatzFrontierAux`) from the private
repo `collatz-frontier` (commit 4d656b9c9c5815305bd391f206c9d3e9587dd395),
file `lean/CollatzFrontier/AffineDrift.lean`, declaration `dyadic_chain_growth`.
No repo module is imported.
-/

namespace CollatzFrontierAux

/-- The scaled representative orbit grows by a nonnegative affine intercept. -/
theorem dyadic_chain_growth (a b : ℕ → ℕ) (k : ℕ)
    (hstep : ∀ i < k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1)) :
    3 ^ k * b 0 ≤ 2 ^ (∑ i ∈ Finset.range k, a i) * b k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hp := ih (fun i hi => hstep i (by omega))
      rw [Finset.sum_range_succ, pow_add, pow_succ]
      calc
        _ ≤ 3 * (2 ^ (∑ i ∈ Finset.range k, a i) * b k) := by nlinarith [hp]
        _ ≤ 2 ^ (∑ i ∈ Finset.range k, a i) * (3 * b k + 1) := by
          calc
            _ ≤ 3 * (2 ^ (∑ i ∈ Finset.range k, a i) * b k) +
                2 ^ (∑ i ∈ Finset.range k, a i) := Nat.le_add_right _ _
            _ = _ := by ring
        _ = _ := by rw [hstep k (by omega)]; ring

end CollatzFrontierAux

open CollatzFrontierAux

theorem solution (a b : ℕ → ℕ) (k e B : ℕ)
    (hstep : ∀ i < k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1))
    (hfinal : 3 * b k + 1 = 2 ^ e * B)
    (hdesc : B ≤ b 0) :
    3 ^ (k + 1) < 2 ^ ((∑ i ∈ Finset.range k, a i) + e) := by
  have hp := dyadic_chain_growth a b k hstep
  have hpow : 0 < 2 ^ (∑ i ∈ Finset.range k, a i) := pow_pos (by decide) _
  have hx : 3 ^ (k + 1) * b 0 <
      2 ^ ((∑ i ∈ Finset.range k, a i) + e) * b 0 := by
    calc
      _ ≤ 3 * (2 ^ (∑ i ∈ Finset.range k, a i) * b k) := by rw [pow_succ]; nlinarith
      _ < 2 ^ (∑ i ∈ Finset.range k, a i) * (3 * b k + 1) := by nlinarith
      _ = 2 ^ ((∑ i ∈ Finset.range k, a i) + e) * B := by rw [hfinal, pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hdesc
  exact Nat.lt_of_mul_lt_mul_right hx
