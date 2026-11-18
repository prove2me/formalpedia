-- Prove2me | solution 1 for BirthdayEntropy.Soundness.role_set_encoding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:36:53.871192+00:00
-- url     : https://prove2.me/submissions/c7f8928d-ea31-4db7-b0a0-4dad00b331cb

import Definitions.Def_BirthdayEntropy_Soundness_Source
noncomputable section
open scoped Classical
open Finset BirthdayEntropy.Soundness

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ), 0 < x → x ≤ 1/2 →
      ∀ (n m b : ℕ), b ≤ m → m ≤ n →
        Real.log (Nat.choose m b : ℝ) ≤
          C * Real.log (Real.exp 1 / x) * (((m : ℝ) - b) + x * b) := by
  refine ⟨1, by norm_num, ?_⟩
  intro x hx hxhalf n m b hbm hmn
  have hchoose : (0 : ℝ) < Nat.choose m b := by exact_mod_cast Nat.choose_pos hbm
  have hpow : (Nat.choose m b : ℝ) * x^(m-b) ≤ (1+x)^m := by
    rw [add_pow]
    have ht := Finset.single_le_sum (f := fun i => (1 : ℝ)^i * x^(m-i) * (Nat.choose m i : ℝ))
      (fun i _ => by positivity) (show b ∈ Finset.range (m+1) by simp; omega)
    simpa [mul_comm] using ht
  have hlog := Real.log_le_log (mul_pos hchoose (pow_pos hx _)) hpow
  rw [Real.log_mul hchoose.ne' (pow_ne_zero _ hx.ne'), Real.log_pow, Real.log_pow] at hlog
  have hlogx : Real.log x ≤ 0 := Real.log_nonpos hx.le (by linarith)
  have hadd : Real.log (1+x) ≤ x := by
    simpa using Real.log_le_sub_one_of_pos (show 0 < 1+x by positivity)
  have hA : Real.log (Real.exp 1 / x) = 1 - Real.log x := by
    rw [Real.log_div (Real.exp_ne_zero _) hx.ne', Real.log_exp]
  rw [one_mul, hA]
  have hnat : ((m - b : ℕ) : ℝ) = (m : ℝ) - b := by norm_cast
  rw [hnat] at hlog
  have hmx := mul_le_mul_of_nonneg_left hadd (show 0 ≤ (m : ℝ) by positivity)
  have hu : 0 ≤ (m : ℝ) - b := sub_nonneg.mpr (by exact_mod_cast hbm)
  have hnonneg : 0 ≤ -Real.log x * (x * b) := mul_nonneg (neg_nonneg.mpr hlogx) (by positivity)
  have hx1 : x ≤ 1 := by linarith
  nlinarith [mul_nonneg hu (sub_nonneg.mpr hx1)]
