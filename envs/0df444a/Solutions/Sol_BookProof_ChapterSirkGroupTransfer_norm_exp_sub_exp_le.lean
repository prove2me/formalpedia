-- Prove2me | solution 1 for BookProof.ChapterSirkGroupTransfer.norm_exp_sub_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T05:57:02.109507+00:00
-- url     : https://prove2.me/submissions/86d82816-85cc-43e6-af4a-8170e74df08d

-- Generated from ChapterSirkGroupTransfer.lean — solution of BookProof.ChapterSirkGroupTransfer.norm_exp_sub_exp_le
import Mathlib
import Definitions.Def_ChapterSirkGroupTransfer
import Theorems.Thm_BookProof_ChapterSirkGroupTransfer_norm_pow_le_of_le
import Theorems.Thm_BookProof_ChapterSirkGroupTransfer_norm_pow_sub_pow_le
open BookProof.ChapterSirkGroupTransfer








noncomputable section


open NormedSpace

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

set_option maxHeartbeats 1000000 in
theorem solution {a b : A} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖exp a - exp b‖ ≤ ‖a - b‖ * Real.exp M := by

  have hM : 0 ≤ M := le_trans (norm_nonneg _) ha
  set f : ℕ → ℝ := fun n => ‖((n.factorial : ℂ))⁻¹ • (a ^ n - b ^ n)‖ with hf
  have hnormsmul : ∀ n : ℕ, f n = (n.factorial : ℝ)⁻¹ * ‖a ^ n - b ^ n‖ := by
    intro n
    simp [hf, norm_smul]
  -- the two exponential series
  have hsa := expSeries_summable' (𝕂 := ℂ) a
  have hsb := expSeries_summable' (𝕂 := ℂ) b
  have hdiff : exp a - exp b = ∑' n : ℕ, ((n.factorial : ℂ))⁻¹ • (a ^ n - b ^ n) := by
    rw [exp_eq_tsum ℂ, ← hsa.tsum_sub hsb]
    simp [smul_sub]
  -- summability of the norms
  have hfsummable : Summable f := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((Real.summable_pow_div_factorial M).mul_left 2)
    rw [hnormsmul n]
    have h1 : ‖a ^ n - b ^ n‖ ≤ M ^ n + M ^ n :=
      le_trans (norm_sub_le _ _) (add_le_add (norm_pow_le_of_le ha n) (norm_pow_le_of_le hb n))
    have h2 : (0 : ℝ) ≤ (n.factorial : ℝ)⁻¹ := by positivity
    calc (n.factorial : ℝ)⁻¹ * ‖a ^ n - b ^ n‖
        ≤ (n.factorial : ℝ)⁻¹ * (M ^ n + M ^ n) := by gcongr
      _ = 2 * (M ^ n / n.factorial) := by ring
  -- the tail bound
  have hstep : ∀ n : ℕ, f (n + 1) ≤ ‖a - b‖ * (M ^ n / n.factorial) := by
    intro n
    rw [hnormsmul (n + 1)]
    have hfac : ((n + 1).factorial : ℝ)⁻¹ * ((n : ℝ) + 1) = (n.factorial : ℝ)⁻¹ := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    have hpos : (0 : ℝ) ≤ ((n + 1).factorial : ℝ)⁻¹ := by positivity
    calc ((n + 1).factorial : ℝ)⁻¹ * ‖a ^ (n + 1) - b ^ (n + 1)‖
        ≤ ((n + 1).factorial : ℝ)⁻¹ * (((n : ℝ) + 1) * M ^ n * ‖a - b‖) := by
          gcongr
          exact norm_pow_sub_pow_le ha hb n
      _ = (((n + 1).factorial : ℝ)⁻¹ * ((n : ℝ) + 1)) * M ^ n * ‖a - b‖ := by ring
      _ = (n.factorial : ℝ)⁻¹ * M ^ n * ‖a - b‖ := by rw [hfac]
      _ = ‖a - b‖ * (M ^ n / n.factorial) := by ring
  have hzero : f 0 = 0 := by simp [hf]
  have hexpM : ∑' n : ℕ, M ^ n / n.factorial = Real.exp M := by
    rw [Real.exp_eq_exp_ℝ, exp_eq_tsum_div]
  calc ‖exp a - exp b‖ = ‖∑' n : ℕ, ((n.factorial : ℂ))⁻¹ • (a ^ n - b ^ n)‖ := by rw [hdiff]
    _ ≤ ∑' n : ℕ, f n := norm_tsum_le_tsum_norm hfsummable
    _ = ∑' n : ℕ, f (n + 1) := by rw [hfsummable.tsum_eq_zero_add, hzero, zero_add]
    _ ≤ ∑' n : ℕ, ‖a - b‖ * (M ^ n / n.factorial) :=
        Summable.tsum_le_tsum hstep (hfsummable.comp_injective (add_left_injective 1))
          ((Real.summable_pow_div_factorial M).mul_left _)
    _ = ‖a - b‖ * Real.exp M := by rw [tsum_mul_left, hexpM]
