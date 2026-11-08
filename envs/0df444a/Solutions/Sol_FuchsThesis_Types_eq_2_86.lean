-- Prove2me | solution 1 for FuchsThesis.Types.eq_2_86
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:30:02.454194+00:00
-- url     : https://prove2.me/submissions/3cba1726-cb2b-44a7-9f99-e88ee3bccc7f

import Mathlib

set_option autoImplicit false

theorem solution (m n : ℕ) :
    (n : ℝ) ^ ((m : ℤ) - (n : ℤ)) ≤ (Nat.factorial m : ℝ) / (Nat.factorial n : ℝ) := by
  rcases le_total n m with h | h
  · have hz : ((m:ℤ) - (n:ℤ)) = ((m - n : ℕ) : ℤ) := by
      rw [Nat.cast_sub h]
    rw [hz, zpow_natCast, le_div_iff₀ (by exact_mod_cast Nat.factorial_pos n)]
    have h1 := Nat.factorial_mul_pow_sub_le_factorial h
    have h2 : ((Nat.factorial n * n ^ (m - n) : ℕ) : ℝ) ≤ (Nat.factorial m : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    linarith
  · have hz : ((m:ℤ) - (n:ℤ)) = -((n - m : ℕ) : ℤ) := by
      rw [Nat.cast_sub h]
      ring
    rw [hz, zpow_neg, zpow_natCast]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hm : m = 0 := by omega
      subst hm
      simp
    · have hd := Nat.factorial_mul_descFactorial (show n - m ≤ n by omega)
      have hnm : n - (n - m) = m := by omega
      rw [hnm] at hd
      have hle := Nat.descFactorial_le_pow n (n - m)
      have hdpos : 0 < n.descFactorial (n - m) := by
        rcases Nat.eq_zero_or_pos (n.descFactorial (n - m)) with h0 | h0
        · rw [h0, mul_zero] at hd
          exact absurd hd.symm (Nat.factorial_pos n).ne'
        · exact h0
      rw [← hd]
      push_cast
      rw [div_mul_cancel_left₀ (by exact_mod_cast (Nat.factorial_pos m).ne')]
      have hdr : (0:ℝ) < (n.descFactorial (n - m) : ℝ) := by exact_mod_cast hdpos
      have hler : (n.descFactorial (n - m) : ℝ) ≤ (n:ℝ) ^ (n - m) := by exact_mod_cast hle
      exact inv_anti₀ hdr hler
