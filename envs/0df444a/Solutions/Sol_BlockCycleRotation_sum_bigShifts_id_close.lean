-- Prove2me | solution 1 for BlockCycleRotation.sum_bigShifts_id_close
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:55:10.056999+00:00
-- url     : https://prove2.me/submissions/d09e470c-81f0-4209-ad45-518d9add4000

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_AllShifts
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Filter Topology Finset Real

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

theorem mem_allShifts {n k : ℕ} : k ∈ allShifts n ↔ k ≤ n ∧ 1 ≤ k ∧ 2 * k ≤ n := by
  simp [allShifts]

theorem allShifts_eq_filter_prime {n : ℕ} (hn : 0 < n) :
    allShifts n = (Finset.Icc 1 n).filter (fun k => 2 * k ≤ n) := by
  ext k
  rw [mem_allShifts, Finset.mem_filter, Finset.mem_Icc]
  omega

theorem sum_Icc_split {n : ℕ} (hn : 0 < n) (f : ℕ → ℕ) :
    ∑ k ∈ Finset.Icc 1 n, f k
      = (∑ k ∈ allShifts n, f k) + ∑ k ∈ bigShifts n, f k := by
  rw [allShifts_eq_filter_prime hn, bigShifts]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem allShifts_eq_Icc (n : ℕ) : allShifts n = Finset.Icc 1 (n / 2) := by
  ext k
  rw [mem_allShifts, Finset.mem_Icc]
  omega

theorem two_mul_sum_Icc (m : ℕ) : 2 * ∑ k ∈ Finset.Icc 1 m, k = m * (m + 1) := by
  have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext k
    rw [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have h : ∑ k ∈ Finset.Icc 1 m, k = ∑ i ∈ Finset.range (m + 1), i := by
    rw [hIcc, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < m + 1)]
    simp
  rw [h]
  have h2 := Finset.sum_range_id_mul_two (m + 1)
  rw [Nat.add_sub_cancel] at h2
  have hcomm : (m + 1) * m = m * (m + 1) := Nat.mul_comm _ _
  omega

theorem two_mul_sum_bigShifts {n : ℕ} (hn : 0 < n) :
    2 * (∑ k ∈ bigShifts n, k) + (n / 2) * (n / 2 + 1) = n * (n + 1) := by
  have hsplit := sum_Icc_split hn (fun k => k)
  rw [allShifts_eq_Icc] at hsplit
  have h1 := two_mul_sum_Icc n
  have h2 := two_mul_sum_Icc (n / 2)
  omega

end BlockCycleRotation

open BlockCycleRotation in
/-- `∑_{k > n/2} k` is `3n²/8` up to `n`. -/
theorem solution {n : ℕ} (hn : 0 < n) :
    |((∑ k ∈ bigShifts n, k : ℕ) : ℝ) - 3 * (n : ℝ) ^ 2 / 8| ≤ (n : ℝ):= by
  have hkey := two_mul_sum_bigShifts hn
  have hm : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2 ▸ by omega
  have hr : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hkeyR : 2 * ((∑ k ∈ bigShifts n, k : ℕ) : ℝ)
      + ((n / 2 : ℕ) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) = (n : ℝ) * ((n : ℝ) + 1) := by
    exact_mod_cast hkey
  have hmR : 2 * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hm
  have hrR : ((n % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ ((n % 2 : ℕ) : ℝ) := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_le]
  constructor <;> nlinarith [hkeyR, hmR, hrR, hr0, hn1]
