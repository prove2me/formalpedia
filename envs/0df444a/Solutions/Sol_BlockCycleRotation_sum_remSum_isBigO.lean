-- Prove2me | solution 1 for BlockCycleRotation.sum_remSum_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:28:02.333149+00:00
-- url     : https://prove2.me/submissions/bd8dc6c7-f5df-43ca-8752-0a9995baf5ae

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_exists_card_divisors_le
import Theorems.Thm_BlockCycleRotation_sum_allShifts_eq
import Theorems.Thm_BlockCycleRotation_heilbron
import Theorems.Thm_BlockCycleRotation_R_isBigO
import Mathlib

open Finset Real

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
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

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
/-- **`∑_{2k ≤ n} remSum(n,k) = C·n² + O(n^{3/2+ε})`.** -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |((∑ k ∈ allShifts n, remSum n k : ℕ) : ℝ) - cConst * (n : ℝ) ^ 2|
        ≤ K * (n : ℝ) ^ (3 / 2 + ε):= by
  obtain ⟨K1, hK1, hR⟩ := R_isBigO hε
  obtain ⟨C0, hC0, hCd⟩ := exists_card_divisors_le hε
  refine ⟨K1 + C0, by positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hRcast : ((Rquad n : ℤ) : ℝ) = ((∑ q ∈ quadruplesAll n, q.2.1 : ℕ) : ℝ) := by
    unfold Rquad; push_cast; ring
  have heil : ((∑ k ∈ allShifts n, remSum n k : ℕ) : ℝ)
      = ((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ)
        + ((∑ q ∈ quadruplesAll n, q.2.1 : ℕ) : ℝ) := by
    exact_mod_cast heilbron hn
  have hgcd : ((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ) ≤ (n : ℝ) * (n.divisors.card : ℝ) := by
    exact_mod_cast sum_gcd_le hn
  have hgcdnn : (0 : ℝ) ≤ ((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ) := by positivity
  have hbound : (n : ℝ) * (n.divisors.card : ℝ) ≤ C0 * (n : ℝ) ^ (3 / 2 + ε) := by
    have h1 : (n : ℝ) * (n.divisors.card : ℝ) ≤ (n : ℝ) * (C0 * (n : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (hCd n hn.ne') (by linarith)
    have h2 : (n : ℝ) * (C0 * (n : ℝ) ^ ε) = C0 * (n : ℝ) ^ (1 + ε) := by
      rw [Real.rpow_add hnpos, Real.rpow_one]; ring
    have h3 : (n : ℝ) ^ (1 + ε) ≤ (n : ℝ) ^ (3 / 2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
    nlinarith [hC0]
  have hRb := hR n hn
  rw [heil, ← hRcast]
  have htri := abs_add_le (((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ))
    (((Rquad n : ℤ) : ℝ) - cConst * (n : ℝ) ^ 2)
  rw [abs_of_nonneg hgcdnn] at htri
  have heq : ((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ) + ((Rquad n : ℤ) : ℝ)
        - cConst * (n : ℝ) ^ 2
      = ((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ)
        + (((Rquad n : ℤ) : ℝ) - cConst * (n : ℝ) ^ 2) := by ring
  rw [heq]
  linarith [htri, hRb, hgcd, hbound]
