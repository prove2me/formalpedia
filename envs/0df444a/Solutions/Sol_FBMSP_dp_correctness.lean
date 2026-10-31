-- Prove2me | solution 1 for FBMSP.dp_correctness
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:08:21.870788+00:00
-- url     : https://prove2.me/submissions/09a4be7d-a0cf-4645-ba8b-fec67db42086

import Definitions.Def_FBMSP_DynamicProgram

open FBMSP

private theorem le_prefixMax_aux (f : ℕ → ℝ) {i n : ℕ} (hi : i ≤ n) :
    f i ≤ prefixMax f n := by
  induction n with
  | zero =>
      have : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      exact le_rfl
  | succ n ih =>
      by_cases h : i ≤ n
      · exact (ih h).trans (le_max_left _ _)
      · have : i = n + 1 := by omega
        subst i
        exact le_max_right _ _

private theorem prefixMax_attained_aux (f : ℕ → ℝ) (n : ℕ) :
    ∃ i, i ≤ n ∧ prefixMax f n = f i := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
      rcases le_total (prefixMax f n) (f (n + 1)) with h | h
      · exact ⟨n + 1, le_rfl, max_eq_right h⟩
      · obtain ⟨i, hi, heq⟩ := ih
        exact ⟨i, Nat.le_trans hi (Nat.le_succ n), (max_eq_left h).trans heq⟩

private theorem intervalDP_attained_aux (W : ℕ → ℕ → ℝ) (k a n : ℕ) :
    IntervalValue W k a n (intervalDP W k a n) := by
  induction k generalizing a n with
  | zero => exact IntervalValue.one a n
  | succ k ih =>
      obtain ⟨i, hi, heq⟩ := prefixMax_attained_aux
        (fun i => intervalDP W k a i + W (a + i) (a + n)) n
      change IntervalValue W (k + 1) a n
        (prefixMax (fun i => intervalDP W k a i + W (a + i) (a + n)) n)
      rw [heq]
      exact IntervalValue.append hi (ih a i)

private theorem intervalValue_le_aux {W : ℕ → ℕ → ℝ}
    {k a n : ℕ} {v : ℝ} (hv : IntervalValue W k a n v) :
    v ≤ intervalDP W k a n := by
  induction hv with
  | one a n => exact le_rfl
  | @append k a n i v hi hv ih =>
      exact (add_le_add ih (le_rfl : W (a + i) (a + n) ≤ W (a + i) (a + n))).trans
        (le_prefixMax_aux (fun j => intervalDP W k a j + W (a + j) (a + n)) hi)

theorem solution (W : ℕ → ℕ → ℝ) (k a n : ℕ) :
    IntervalValue W k a n (intervalDP W k a n) ∧
      ∀ v, IntervalValue W k a n v → v ≤ intervalDP W k a n := by
  exact ⟨intervalDP_attained_aux W k a n, fun _ hv => intervalValue_le_aux hv⟩
