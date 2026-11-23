-- Prove2me | solution 1 for BroughanRH.robinEleventhPower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:48:31.375487+00:00
-- url     : https://prove2.me/submissions/6605908b-2809-46e6-b4c2-9d5b4c925be9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BroughanRH_robin
import Mathlib

/-- Robin's inequality at `2^k` for `k = 11, 12`, checked directly. -/
lemma robin_two_pow (k : ℕ) (hk : k = 11 ∨ k = 12) :
    ((ArithmeticFunction.sigma 1 (2^k) : ℕ) : ℝ) <
      Real.exp Real.eulerMascheroniConstant * ((2^k : ℕ) : ℝ) * Real.log (Real.log ((2^k : ℕ) : ℝ)) := by
  have hg := Real.one_half_lt_eulerMascheroniConstant
  have hl2 := Real.log_two_gt_d9
  have he : (1.5 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
    have := Real.add_one_le_exp Real.eulerMascheroniConstant; linarith
  have hlog : Real.log ((2^k : ℕ) : ℝ) = k * Real.log 2 := by
    push_cast; rw [Real.log_pow]
  have hk11 : (11 : ℝ) ≤ k := by rcases hk with rfl | rfl <;> norm_num
  have h4 : (4 : ℝ) ≤ Real.log ((2^k : ℕ) : ℝ) := by rw [hlog]; nlinarith
  have hll : 2 * Real.log 2 ≤ Real.log (Real.log ((2^k : ℕ) : ℝ)) := by
    rw [← Real.log_rpow (by norm_num)]
    apply Real.log_le_log (by positivity)
    norm_num; linarith
  have hpos : (0:ℝ) < ((2^k : ℕ) : ℝ) := by positivity
  rcases hk with rfl | rfl
  · rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
    norm_num [Finset.sum_range_succ] at hll ⊢
    nlinarith
  · rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
    norm_num [Finset.sum_range_succ] at hll ⊢
    nlinarith

theorem solution :
    ∀ n : ℕ, 2 < n → (∃ p : ℕ, p.Prime ∧ p^11 ∣ n) → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  intro n hn ⟨p, hp, hdvd⟩
  rcases lt_or_ge 5040 n with h | h
  · exact BroughanRH.robin n h
  · have hle : p^11 ≤ n := Nat.le_of_dvd (by omega) hdvd
    have hp2 : p = 2 := by
      by_contra hne
      have h3 : 3 ≤ p := by have := hp.two_le; omega
      have : 3^11 ≤ p^11 := Nat.pow_le_pow_left h3 11
      norm_num at this; omega
    subst hp2
    obtain ⟨m, rfl⟩ := hdvd
    have hm : m = 1 ∨ m = 2 := by
      norm_num at h hn; omega
    rcases hm with rfl | rfl
    · rw [mul_one]; exact robin_two_pow 11 (Or.inl rfl)
    · rw [show 2^11 * 2 = 2^12 by norm_num]; exact robin_two_pow 12 (Or.inr rfl)
