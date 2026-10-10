-- Prove2me | solution 1 for Erdos68.factorial_moment_partial_sum_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-10T00:19:33.350069+00:00
-- url     : https://prove2.me/submissions/5f675e47-387c-4557-9d17-d5c70acc20b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Erdos68_factorial_moment_integer_separation
import Theorems.Thm_Erdos68_factorial_tail_sharp_window

open scoped BigOperators

open Erdos68

/-!
Reduction of `Erdos68.factorial_moment_partial_sum_bound` to two child lemmas:

* `Erdos68.factorial_tail_sharp_window` — the factorial-scaled tail
  `t_M = M! * ∑_{n>M} 1/(n!-1)` lies in the open window `(1/(M+1), 1/M)`.
* `Erdos68.factorial_moment_integer_separation` — `M! * x`, with
  `x = ∑_{n≥2} 1/(n!-1)`, is never within `1/(M(M+1))` of an integer.

If `{A_M}` (fractional part of `A_M = ∑_{n=2}^M M!/(n!-1)`) lay in
`(1 - 1/M, 1 - 1/(M+1))`, then `δ := ⌊A_M⌋ + 1 - A_M` would lie in
`(1/(M+1), 1/M)`; since `M! * x = A_M + t_M`, the integer `⌊A_M⌋ + 1`
would be within `1/(M(M+1))` of `M! * x`, contradicting the separation
lemma.

The summability helpers below are reproduced from the accepted platform
reduction of `Erdos68.irrational_from_tail_bounds`
(submission `054f0b09-45e0-465c-9650-8d089f4cd21f`).
-/

lemma e68_fact_sub_one_pos {m : ℕ} (hm : 2 ≤ m) : (0 : ℝ) < (m.factorial : ℝ) - 1 := by
  have : 1 < m.factorial := Nat.one_lt_factorial.mpr (by omega)
  have : (1 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast this
  linarith

lemma e68_key_le {s : ℕ} (n : ℕ) (hs : 2 ≤ s) :
    ((s.factorial : ℝ) - 1) * ((s : ℝ) + 1) ^ n ≤ ((n + s).factorial : ℝ) - 1 := by
  have h1 : s.factorial * (s + 1) ^ n ≤ (s + n).factorial :=
    Nat.factorial_mul_pow_le_factorial
  have h1' : (s.factorial : ℝ) * ((s : ℝ) + 1) ^ n ≤ ((n + s).factorial : ℝ) := by
    rw [add_comm n s]; exact_mod_cast h1
  have h2 : (1 : ℝ) ≤ ((s : ℝ) + 1) ^ n :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg s : (0:ℝ) ≤ s)])
  nlinarith

lemma e68_term_nonneg {s : ℕ} (n : ℕ) (hs : 2 ≤ s) :
    0 ≤ 1 / (((n + s).factorial : ℝ) - 1) :=
  le_of_lt (one_div_pos.mpr (e68_fact_sub_one_pos (by omega)))

lemma e68_term_le {s : ℕ} (n : ℕ) (hs : 2 ≤ s) :
    1 / (((n + s).factorial : ℝ) - 1) ≤
      (1 / ((s.factorial : ℝ) - 1)) * (1 / ((s : ℝ) + 1)) ^ n := by
  have hpos : 0 < ((s.factorial : ℝ) - 1) * ((s : ℝ) + 1) ^ n :=
    mul_pos (e68_fact_sub_one_pos hs) (by positivity)
  rw [div_pow, one_pow, one_div_mul_one_div]
  exact one_div_le_one_div_of_le hpos (e68_key_le n hs)

lemma e68_ratio_lt {s : ℕ} (hs : 2 ≤ s) : 1 / ((s : ℝ) + 1) < 1 := by
  rw [div_lt_one (by positivity)]
  have : (2 : ℝ) ≤ s := by exact_mod_cast hs
  linarith

lemma e68_summable {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun n : ℕ => 1 / (((n + s).factorial : ℝ) - 1)) :=
  Summable.of_nonneg_of_le (fun n => e68_term_nonneg n hs) (fun n => e68_term_le n hs)
    ((summable_geometric_of_lt_one (by positivity) (e68_ratio_lt hs)).mul_left _)

theorem solution (M : ℕ) (hM : 3 ≤ M)
    (hlo : 1 - 1 / (M : ℚ) <
        Int.fract (∑ n ∈ Finset.range (M - 1), (M.factorial : ℚ) / (((n + 2).factorial : ℚ) - 1)))
    (hhi : Int.fract (∑ n ∈ Finset.range (M - 1), (M.factorial : ℚ) / (((n + 2).factorial : ℚ) - 1)) <
        1 - 1 / ((M : ℚ) + 1)) :
    False := by
  -- Notation: `A` is the rational moment sum, `a` its floor, `δ := a + 1 - A`.
  set A : ℚ := ∑ n ∈ Finset.range (M - 1), (M.factorial : ℚ) / (((n + 2).factorial : ℚ) - 1)
    with hAdef
  try simp only [← hAdef] at hlo hhi
  set a : ℤ := Int.floor A with hadef
  have hfr : (a : ℚ) + Int.fract A = A := by rw [hadef, Int.floor_add_fract]
  -- Step 1: δ = a + 1 - A = 1 - fract(A) lies in the open window (1/(M+1), 1/M).
  have hδ : 1 / ((M : ℚ) + 1) < (a + 1 : ℚ) - A ∧ (a + 1 : ℚ) - A < 1 / (M : ℚ) := by
    have hδeq : (a + 1 : ℚ) - A = 1 - Int.fract A := by linarith [hfr]
    constructor
    · rw [hδeq]; linarith
    · rw [hδeq]; linarith
  have eL1 : (1 : ℝ) / ((M : ℝ) + 1) = ((1 / ((M : ℚ) + 1) : ℚ) : ℝ) := by push_cast; rfl
  have eR1 : ((a + 1 : ℤ) : ℝ) - (A : ℝ) = (((a + 1 : ℚ) - A : ℚ) : ℝ) := by push_cast; rfl
  have eR2 : (1 : ℝ) / (M : ℝ) = ((1 / (M : ℚ) : ℚ) : ℝ) := by push_cast; rfl
  have hδR1 : (1 : ℝ) / ((M : ℝ) + 1) < ((a + 1 : ℤ) : ℝ) - (A : ℝ) := by
    rw [eL1, eR1]; exact Rat.cast_lt.mpr hδ.1
  have hδR2 : ((a + 1 : ℤ) : ℝ) - (A : ℝ) < 1 / (M : ℝ) := by
    rw [eR1, eR2]; exact Rat.cast_lt.mpr hδ.2
  -- Step 2: split the series at M.
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / ((n + 2).factorial - 1)) := e68_summable le_rfl
  have htail_eq : (∑' i : ℕ, (1 : ℝ) / (((i + (M - 1)) + 2).factorial - 1)) =
      ∑' i : ℕ, (1 : ℝ) / ((i + M + 1).factorial - 1) := by
    congr 1; funext i; rw [show (i + (M - 1) + 2 : ℕ) = i + M + 1 by omega]
  have hsplit' : (∑ i ∈ Finset.range (M - 1), (1 : ℝ) / ((i + 2).factorial - 1)) +
      (∑' i : ℕ, (1 : ℝ) / ((i + M + 1).factorial - 1)) =
      ∑' n : ℕ, (1 : ℝ) / ((n + 2).factorial - 1) := by
    rw [← htail_eq]; exact hsum.sum_add_tsum_nat_add (M - 1)
  have hcast : (A : ℝ) = (M.factorial : ℝ) *
      ∑ i ∈ Finset.range (M - 1), (1 : ℝ) / ((i + 2).factorial - 1) := by
    rw [hAdef]; push_cast; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_one_div]
  -- Step 3: the scaled tail t = M!·Σ_{n>M} 1/(n!-1) lies in the same window.
  obtain ⟨htlo, hthi⟩ := factorial_tail_sharp_window M hM
  set t := (M.factorial : ℝ) * ∑' n : ℕ, (1 : ℝ) / ((n + M + 1).factorial - 1) with htdef
  try simp only [← htdef] at htlo hthi
  -- Step 4: the factorial moment identity  M!·x = A + t.
  have hmain : (M.factorial : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((n + 2).factorial - 1)) = (A : ℝ) + t := by
    have h1 := congrArg ((M.factorial : ℝ) * ·) hsplit'
    rw [mul_add, ← hcast, ← htdef] at h1
    exact h1.symm
  -- Step 5: (a+1) - M!·x = δ - t, hence |M!·x - (a+1)| < 1/(M(M+1)).
  have heq : (M.factorial : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((n + 2).factorial - 1)) - ((a + 1 : ℤ) : ℝ)
      = t - (((a + 1 : ℤ) : ℝ) - (A : ℝ)) := by
    rw [hmain]; ring
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast show (0 : ℕ) < M from Nat.lt_of_lt_of_le (by decide) hM
  have hM0 : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have hM1 : (M : ℝ) + 1 ≠ 0 := by linarith
  have hM01 : (M : ℝ) * ((M : ℝ) + 1) ≠ 0 := mul_ne_zero hM0 hM1
  have e1 : (1 : ℝ) / ((M : ℝ) + 1) - 1 / (M : ℝ) = -(1 / ((M : ℝ) * ((M : ℝ) + 1))) := by
    field_simp; ring
  have e2 : (1 : ℝ) / (M : ℝ) - 1 / ((M : ℝ) + 1) = 1 / ((M : ℝ) * ((M : ℝ) + 1)) := by
    field_simp; ring
  have habs : |((M.factorial : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((n + 2).factorial - 1)))
      - ((a + 1 : ℤ) : ℝ)| < 1 / ((M : ℝ) * ((M : ℝ) + 1)) := by
    rw [heq, abs_lt]
    constructor
    · linarith [htlo, hδR2, e1]
    · linarith [hthi, hδR1, e2]
  -- Step 6: contradict the separation lemma at m = a + 1.
  have hsep := factorial_moment_integer_separation M hM (a + 1)
  linarith
