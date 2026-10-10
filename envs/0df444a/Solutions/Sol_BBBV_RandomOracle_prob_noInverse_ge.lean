-- Prove2me | solution 1 for BBBV.RandomOracle.prob_noInverse_ge
-- status  : ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-10T01:05:20.280455+00:00
-- url     : https://prove2.me/submissions/b00ee818-4592-4dc6-aa39-bdbfd95c4394

import Mathlib
import Definitions.Def_BBBV_RandomOracle_QueryModel

open BBBV.RandomOracle

/-- `(1 - 1/2^n)^{2^n} ≥ 1/4` for `n ≥ 1`. -/
lemma quarter_le_pow_bbbv (n : ℕ) (hn : 1 ≤ n) :
    (1 / 4 : ℝ) ≤ (((2 : ℝ) ^ n - 1) / 2 ^ n) ^ (2 ^ n) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hmpos : (0 : ℝ) < 2 ^ n := by positivity
    have hm : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have h2 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have hkey : ((2 : ℝ) ^ n - 1) / 2 ^ n ≤ ((2 * 2 ^ n - 1) / (2 * 2 ^ n)) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ hmpos (by positivity)]
      nlinarith
    have hexp : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [h2, hexp, pow_mul]
    calc (1 / 4 : ℝ) ≤ (((2 : ℝ) ^ n - 1) / 2 ^ n) ^ (2 ^ n) := ih
      _ ≤ (((2 * 2 ^ n - 1) / (2 * 2 ^ n)) ^ 2) ^ (2 ^ n) :=
          pow_le_pow_left₀ (by apply div_nonneg <;> linarith) hkey _

open Classical in
theorem solution {n : ℕ} (hn : 1 ≤ n) :
    ((Finset.univ.filter fun A : Str n → Str n => NoInverse A).card : ℝ) /
        (Fintype.card (Str n → Str n) : ℝ) = (((2 : ℝ) ^ n - 1) / 2 ^ n) ^ (2 ^ n) ∧
      (1 / 4 : ℝ) ≤ (((2 : ℝ) ^ n - 1) / 2 ^ n) ^ (2 ^ n) := by
  refine ⟨?_, quarter_le_pow_bbbv n hn⟩
  have hcardStr : Fintype.card (Str n) = 2 ^ n := by simp [Str]
  have hfilter : (Finset.univ.filter fun A : Str n → Str n => NoInverse A) =
      Fintype.piFinset (fun _ : Str n => Finset.univ.erase (ones n)) := by
    ext A
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    simp only [Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, and_true, NoInverse]
  have hcard1 : (Finset.univ.erase (ones n)).card = 2 ^ n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardStr]
  rw [hfilter, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, hcardStr, hcard1,
    Fintype.card_fun, hcardStr]
  have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  push_cast [Nat.cast_sub h1]
  rw [div_pow]
