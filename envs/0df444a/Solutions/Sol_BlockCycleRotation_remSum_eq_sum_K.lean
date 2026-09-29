-- Prove2me | solution 1 for BlockCycleRotation.remSum_eq_sum_K
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:54:09.134519+00:00
-- url     : https://prove2.me/submissions/73685cd0-81cf-48f8-978c-5dbb08ebc2fa

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_cf
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

/-- The defining recursion, in the form we actually use. -/
theorem remSum_of_pos {k : ℕ} (n : ℕ) (hk : k ≠ 0) :
    remSum n k = k + remSum k (n % k) := by
  rw [remSum]; simp [hk]

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem cf_of_pos {a a' : ℕ} (h : a' ≠ 0) :
    cf a a' = cf a' (a % a') ++ [a / a'] := by rw [cf]; simp [h]

end BlockCycleRotation

open BlockCycleRotation in
/-- **Equation (eq. RemainderSum).**  For coprime `n > k ≥ 1`,

  `remSum n k = ∑_{j < |cf n k|} K ((cf n k).take j)`.

The remainders in the Euclidean algorithm are the continuants of the prefixes
of the expansion. -/
theorem solution : ∀ k n : ℕ, 1 ≤ k → k < n → Nat.gcd n k = 1 →
    remSum n k = ∑ j ∈ Finset.range (cf n k).length, K ((cf n k).take j):= by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk1 hkn hgcd
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have hk : k = 1 := by omega
      subst hk
      have hcf : cf n 1 = [n] := by
        rw [cf_of_pos (by norm_num), Nat.mod_one, cf_zero, Nat.div_one]
        simp
      rw [hcf, remSum_of_pos n (by norm_num)]
      simp [Nat.mod_one]
    · have hkne : k ≠ 0 := by omega
      have hrlt : n % k < k := Nat.mod_lt _ (by omega)
      have hr1 : 1 ≤ n % k := by
        rcases Nat.eq_zero_or_pos (n % k) with h0 | h0
        · exfalso
          have hg : Nat.gcd n k = k := Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h0)
          omega
        · exact h0
      have hgcd' : Nat.gcd k (n % k) = 1 := by
        rw [← hgcd, Nat.gcd_comm n k, Nat.gcd_rec k n]
        exact Nat.gcd_comm _ _
      have hM : K (cf k (n % k)) = k := (K_cf (n % k) k hr1 hrlt hgcd').1
      have hIH := ih (n % k) hrlt k hr1 hrlt hgcd'
      rw [remSum_of_pos n hkne, hIH, cf_of_pos hkne, List.length_append,
        List.length_singleton, Finset.sum_range_succ]
      have h1 : ∀ j ∈ Finset.range (cf k (n % k)).length,
          K ((cf k (n % k) ++ [n / k]).take j) = K ((cf k (n % k)).take j) := by
        intro j hj
        rw [List.take_append_of_le_length (Nat.le_of_lt (Finset.mem_range.1 hj))]
      rw [Finset.sum_congr rfl h1, List.take_left, hM]
      ring
