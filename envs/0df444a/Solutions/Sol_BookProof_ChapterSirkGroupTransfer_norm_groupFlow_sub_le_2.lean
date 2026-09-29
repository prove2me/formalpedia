-- Prove2me | solution 2 for BookProof.ChapterSirkGroupTransfer.norm_groupFlow_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:37:11.540001+00:00
-- url     : https://prove2.me/submissions/0e2bd023-414d-432a-8ada-28304f4b04d1

-- Generated from ChapterSirkGroupTransfer.lean — solution of BookProof.ChapterSirkGroupTransfer.norm_groupFlow_sub_le
import Mathlib
import Definitions.Def_ChapterSirkGroupTransfer
import Theorems.Thm_BookProof_ChapterSirkGroupTransfer_norm_exp_sub_exp_le
open BookProof.ChapterSirkGroupTransfer








noncomputable section


open NormedSpace

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

set_option maxHeartbeats 1000000 in
theorem solution {a b : A} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (t : ℝ) :
    ‖groupFlow a t - groupFlow b t‖ ≤ |t| * ‖a - b‖ * Real.exp (|t| * M) := by

  have hM : 0 ≤ M := le_trans (norm_nonneg _) ha
  have hc : ‖(-(t : ℂ) * Complex.I)‖ = |t| := by
    simp [Complex.norm_real]
  have ha' : ‖(-(t : ℂ) * Complex.I) • a‖ ≤ |t| * M := by
    rw [norm_smul, hc]
    exact mul_le_mul_of_nonneg_left ha (abs_nonneg t)
  have hb' : ‖(-(t : ℂ) * Complex.I) • b‖ ≤ |t| * M := by
    rw [norm_smul, hc]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg t)
  have hsub : (-(t : ℂ) * Complex.I) • a - (-(t : ℂ) * Complex.I) • b
      = (-(t : ℂ) * Complex.I) • (a - b) := by
    rw [smul_sub]
  have := norm_exp_sub_exp_le ha' hb'
  rw [hsub, norm_smul, hc] at this
  simpa [groupFlow, mul_assoc] using this
