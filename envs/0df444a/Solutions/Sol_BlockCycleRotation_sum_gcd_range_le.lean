-- Prove2me | solution 1 for BlockCycleRotation.sum_gcd_range_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:02:59.859267+00:00
-- url     : https://prove2.me/submissions/a405d144-71b8-469f-b03f-c861daa2a697

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_sum_allShifts_eq
import Theorems.Thm_BlockCycleRotation_sum_min_eq
import Mathlib

open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

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

/-- Shifting the first argument by the second does not change the gcd. -/
theorem gcd_add_left (k r : ℕ) : Nat.gcd (k + r) r = Nat.gcd k r := by
  rw [Nat.gcd_comm (k + r) r, Nat.gcd_comm k r]
  exact Nat.gcd_add_self_right r k

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

theorem gcd_min_self_sub {n k : ℕ} (hk : k ≤ n) :
    Nat.gcd n (min k (n - k)) = Nat.gcd n k := by
  rcases le_total k (n - k) with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h]
    calc Nat.gcd n (n - k) = Nat.gcd (k + (n - k)) (n - k) := by congr 1; omega
      _ = Nat.gcd k (n - k) := gcd_add_left k (n - k)
      _ = Nat.gcd (n - k) k := Nat.gcd_comm _ _
      _ = Nat.gcd ((n - k) + k) k := (gcd_add_left (n - k) k).symm
      _ = Nat.gcd n k := by congr 1; omega

end BlockCycleRotation

open BlockCycleRotation in
theorem solution {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ Finset.range n, Nat.gcd n k ≤ n + 2 * (n * n.divisors.card):= by
  have hsplit : ∑ k ∈ Finset.range n, Nat.gcd n k
      = Nat.gcd n 0 + ∑ k ∈ Finset.Ico 1 n, Nat.gcd n k := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn]
  have hmin : ∀ k ∈ Finset.Ico 1 n, Nat.gcd n k = Nat.gcd n (min k (n - k)) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact (gcd_min_self_sub (le_of_lt hk.2)).symm
  have hdouble := sum_min_eq hn (fun j => Nat.gcd n j)
  have hle : ∑ k ∈ Finset.Ico 1 n, Nat.gcd n (min k (n - k))
      ≤ 2 * ∑ j ∈ allShifts n, Nat.gcd n j := by
    rw [← hdouble]
    exact Nat.le_add_right _ _
  have hall := sum_gcd_le hn
  rw [hsplit, Finset.sum_congr rfl hmin, Nat.gcd_zero_right]
  have : 2 * ∑ j ∈ allShifts n, Nat.gcd n j ≤ 2 * (n * n.divisors.card) :=
    Nat.mul_le_mul_left 2 hall
  omega
