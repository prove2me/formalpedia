-- Prove2me | solution 1 for BlockCycleRotation.invquant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:09:34.856857+00:00
-- url     : https://prove2.me/submissions/714f545a-e7a1-406e-b493-c83b93f2ca63

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_exists_card_divisors_le
import Theorems.Thm_BlockCycleRotation_sum_allShifts_eq
import Theorems.Thm_BlockCycleRotation_heilbron
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

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

theorem mem_shifts {n k : ℕ} :
    k ∈ shifts n ↔ k ≤ n ∧ 1 ≤ k ∧ 2 * k ≤ n ∧ Nat.gcd n k = 1 := by
  simp [shifts]

/-- The gcds, aggregated over the gcd. -/
theorem sum_gcd_allShifts {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, Nat.gcd n k = ∑ g ∈ n.divisors, g * (shifts (n / g)).card := by
  rw [sum_allShifts_eq hn (fun g _ => g)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The shifts of `m` number at most `m`. -/
theorem card_shifts_le (m : ℕ) : (shifts m).card ≤ m := by
  have hsub : shifts m ⊆ Finset.Icc 1 m := by
    intro k hk
    obtain ⟨hkm, hk1, hk2, -⟩ := mem_shifts.1 hk
    exact Finset.mem_Icc.2 ⟨hk1, hkm⟩
  calc (shifts m).card ≤ (Finset.Icc 1 m).card := Finset.card_le_card hsub
    _ = m := by simp

/-- **`∑ gcd(n,k) ≤ n · d(n)`.** -/
theorem sum_gcd_le {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, Nat.gcd n k ≤ n * n.divisors.card := by
  rw [sum_gcd_allShifts hn, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_le_sum fun g hg => ?_
  obtain ⟨hgn, -⟩ := Nat.mem_divisors.1 hg
  have hmul : g * (n / g) = n := Nat.mul_div_cancel' hgn
  calc g * (shifts (n / g)).card ≤ g * (n / g) := Nat.mul_le_mul_left _ (card_shifts_le _)
    _ = n := hmul
    _ = n * 1 := (Nat.mul_one n).symm

end BlockCycleRotation

open BlockCycleRotation in
/-- **Equation (invquant).**  The `∑ gcd(n,k)` term of (eq. heilbron) is
`O(n^{1+ε})`, so `∑_{k} remSum n k` and `R(n)` differ by that much. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ((∑ k ∈ allShifts n, remSum n k : ℕ) : ℝ)
          - ((∑ q ∈ quadruplesAll n, q.2.1 : ℕ) : ℝ)
        ≤ C * (n : ℝ) ^ (1 + ε):= by
  obtain ⟨C, hC, hCd⟩ := exists_card_divisors_le hε
  refine ⟨C, hC, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiff := heilbron hn
  have h1 : ((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ) ≤ (n : ℝ) * (n.divisors.card : ℝ) := by
    exact_mod_cast sum_gcd_le hn
  have h2 : ((∑ k ∈ allShifts n, remSum n k : ℕ) : ℝ)
      = ((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ)
        + ((∑ q ∈ quadruplesAll n, q.2.1 : ℕ) : ℝ) := by exact_mod_cast hdiff
  have h3 : (n : ℝ) * (n.divisors.card : ℝ) ≤ (n : ℝ) * (C * (n : ℝ) ^ ε) :=
    mul_le_mul_of_nonneg_left (hCd n hn.ne') hn'.le
  have hrpow : (n : ℝ) ^ (1 + ε) = (n : ℝ) * (n : ℝ) ^ ε := by
    rw [Real.rpow_add hn', Real.rpow_one]
  rw [hrpow]
  linarith
