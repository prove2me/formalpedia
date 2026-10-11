-- Prove2me | solution 1 for BookProof.ChapterShannonSampling.hasSum_sq_samples
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:32:52.337719+00:00
-- url     : https://prove2.me/submissions/7bcf53da-1d3b-463c-a3a0-d4153ac23c57

-- Generated from ChapterShannonSampling.lean — solution of BookProof.ChapterShannonSampling.hasSum_sq_samples
import Mathlib
import Definitions.Def_ChapterShannonSampling
import Theorems.Thm_BookProof_ChapterShannonSampling_bandSignal_sample
import Theorems.Thm_BookProof_ChapterShannonSampling_integral_haar_eq_real
open BookProof.ChapterShannonSampling




open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

set_option maxHeartbeats 1000000 in
theorem solution (F : Lp ℂ 2 (haarAddCircle (T := T))) :
    HasSum (fun n : ℤ => ‖bandSignal (T := T) (F : AddCircle T → ℂ) (n / T)‖ ^ 2)
      (T * ∫ ξ in (-(T / 2))..(-(T / 2) + T), ‖(F : AddCircle T → ℂ) ξ‖ ^ 2) := by

  have hT0 : (0 : ℝ) < T := hT.out
  have hpar := (hasSum_sq_fourierCoeff F).mul_left (T ^ 2)
  have hterm : ∀ n : ℤ, T ^ 2 * ‖fourierCoeff (F : AddCircle T → ℂ) n‖ ^ 2
      = ‖bandSignal (T := T) (F : AddCircle T → ℂ) (-((n : ℝ) / T))‖ ^ 2 := by
    intro n
    rw [bandSignal_sample, norm_mul, mul_pow]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  simp_rw [hterm] at hpar
  have hsum := (Equiv.neg ℤ).hasSum_iff.mpr hpar
  have hrhs : T ^ 2 * ∫ z : AddCircle T, ‖(F : AddCircle T → ℂ) z‖ ^ 2 ∂haarAddCircle
      = T * ∫ ξ in (-(T / 2))..(-(T / 2) + T), ‖(F : AddCircle T → ℂ) ξ‖ ^ 2 := by
    rw [← integral_haar_eq_real (fun z => ‖(F : AddCircle T → ℂ) z‖ ^ 2)]
    ring
  rw [hrhs] at hsum
  refine hsum.congr_fun fun n => ?_
  simp only [Function.comp_apply, Equiv.neg_apply]
  push_cast
  rw [show -(-(n : ℝ) / T) = (n : ℝ) / T from by ring]
