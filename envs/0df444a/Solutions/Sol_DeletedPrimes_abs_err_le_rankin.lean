-- Prove2me | solution 1 for DeletedPrimes.abs_err_le_rankin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:07:56.547684+00:00
-- url     : https://prove2.me/submissions/8f3f418e-3a3c-461f-a93f-2c90e4134f1c

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_summable_abs_muS_div
import Theorems.Thm_DeletedPrimes_summable_muS_div
import Theorems.Thm_DeletedPrimes_rankin_count
import Theorems.Thm_DeletedPrimes_rankin_tail
import Theorems.Thm_DeletedPrimes_abs_saw_le
import Theorems.Thm_DeletedPrimes_legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (hS : ∀ p ∈ S, p.Prime) {σ : ℝ}
    (hsum : Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ)) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (h1 : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-1 : ℝ))) {x : ℝ} (hx : 1 ≤ x) :
    |err S x| ≤ 2 * unitSum S σ * x ^ σ := by
  have hx0 : 0 < x := by linarith
  rw [legendre hS (summable_muS_div h1) hx]
  have hK := rankin_count hsum hσ0 hx
  have hA : |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) * saw (x / d)| ≤
      1 / 2 * (unitSum S σ * x ^ σ) := by
    calc |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) * saw (x / d)|
        ≤ ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, |(muS S d : ℝ) * saw (x / d)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, |(muS S d : ℝ)| * (1 / 2) := by
          refine Finset.sum_le_sum fun d _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_saw_le _) (abs_nonneg _)
      _ = 1 / 2 * ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, |(muS S d : ℝ)| := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ 1 / 2 * (unitSum S σ * x ^ σ) := mul_le_mul_of_nonneg_left hK (by norm_num)
  have hM : |mertensS S x| ≤ unitSum S σ * x ^ σ :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) hK
  have hT : |∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0)| ≤ unitSum S σ * x ^ (σ - 1) := by
    have hle : ∀ d : ℕ, ‖(if x < d then (muS S d : ℝ) / d else 0)‖ ≤ |(muS S d : ℝ) / d| := by
      intro d; split_ifs
      · exact le_rfl
      · simp
    have hs : Summable fun d : ℕ => ‖(if x < d then (muS S d : ℝ) / d else 0)‖ :=
      (summable_abs_muS_div h1).of_nonneg_of_le (fun _ => norm_nonneg _) hle
    calc |∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0)|
        = ‖∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0)‖ := rfl
      _ ≤ ∑' d : ℕ, ‖(if x < d then (muS S d : ℝ) / d else 0)‖ := norm_tsum_le_tsum_norm hs
      _ = ∑' d : ℕ, (if x < d then |(muS S d : ℝ)| / d else 0) := by
          refine tsum_congr fun d => ?_
          split_ifs
          · rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
          · simp
      _ ≤ unitSum S σ * x ^ (σ - 1) := rankin_tail hsum hσ1 hx
  have hxT : |x * ∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0)| ≤ unitSum S σ * x ^ σ := by
    rw [abs_mul, abs_of_pos hx0]
    calc x * |∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0)|
        ≤ x * (unitSum S σ * x ^ (σ - 1)) := mul_le_mul_of_nonneg_left hT hx0.le
      _ = unitSum S σ * x ^ σ := by
          rw [Real.rpow_sub_one hx0.ne']
          field_simp
  have e1 := abs_le.mp hA
  have e2 := abs_le.mp hM
  have e3 := abs_le.mp hxT
  rw [abs_le]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]
end DeletedPrimes
