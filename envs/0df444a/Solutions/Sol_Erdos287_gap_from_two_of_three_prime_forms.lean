-- Prove2me | solution 1 for Erdos287.gap_from_two_of_three_prime_forms
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T03:30:33.591529+00:00
-- url     : https://prove2.me/submissions/e411bf59-c503-4edb-b761-a54b79d72134

import Mathlib
import Theorems.Thm_Erdos287_prime_power_pair_excludes_band

set_option autoImplicit false

/-- Two prime values in a specific triple certify an explicit interval of maxima. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (t : ℕ) (ht : 5 ≤ t)
    (hlo : 24 * t + 4 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 29 * t)
    (hprime : (Nat.Prime (6 * t + 1) ∧ Nat.Prime (8 * t + 1)) ∨
      (Nat.Prime (6 * t + 1) ∧ Nat.Prime (12 * t + 1)) ∨
      (Nat.Prime (8 * t + 1) ∧ Nat.Prime (12 * t + 1))) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  let M := f (k - 1)
  have hcof : (∑ j ∈ Finset.Icc 1 4, Nat.lcmUpto 4 / j) = 25 := by decide
  have hexp : (5 / 2 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hband (x : ℕ) (hx₁ : 12 * t ≤ x) (hx₂ : x ≤ 24 * t + 3)
      (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
      (hpl : 6 * t + 1 ≤ p) (hql : 6 * t + 1 ≤ q)
      (hpx : p ∣ x) (hqx : q ∣ x + 1) :
      ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
    have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hsmall : (M : ℝ) < (5 / 2 : ℝ) * x := by
      have h₁ : (M : ℝ) ≤ 29 * t := by exact_mod_cast hhi
      have h₂ : 12 * (t : ℝ) ≤ x := by exact_mod_cast hx₁
      have h₃ : (5 : ℝ) ≤ t := by exact_mod_cast ht
      linarith
    refine Erdos287.prime_power_pair_excludes_band k hk f hf1 hmono hsum x (by omega)
      (by omega) (hsmall.trans (mul_lt_mul_of_pos_right hexp hxR))
      p q 1 1 4 4 hp hq le_rfl le_rfl
      (by simpa using hpx) (by simpa using hqx) (by omega) (by omega)
      (by simp only [pow_one]; omega) (by simp only [pow_one]; omega)
      (by rw [hcof]; omega) (by rw [hcof]; omega)
  rcases hprime with ⟨h₆, h₈⟩ | ⟨h₆, h₁₂⟩ | ⟨h₈, h₁₂⟩
  · refine hband (24 * t + 3) (by omega) le_rfl (8 * t + 1) (6 * t + 1) h₈ h₆
      (by omega) le_rfl ?_ ?_
    · exact ⟨3, by ring⟩
    · exact ⟨4, by ring⟩
  · refine hband (12 * t + 1) (by omega) (by omega) (12 * t + 1) (6 * t + 1) h₁₂ h₆
      (by omega) le_rfl dvd_rfl ?_
    exact ⟨2, by ring⟩
  · refine hband (24 * t + 2) (by omega) (by omega) (12 * t + 1) (8 * t + 1) h₁₂ h₈
      (by omega) (by omega) ?_ ?_
    · exact ⟨2, by ring⟩
    · exact ⟨3, by ring⟩

