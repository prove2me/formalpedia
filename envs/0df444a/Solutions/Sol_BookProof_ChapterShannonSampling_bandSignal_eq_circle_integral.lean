-- Prove2me | solution 1 for BookProof.ChapterShannonSampling.bandSignal_eq_circle_integral
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:31:08.710191+00:00
-- url     : https://prove2.me/submissions/64a9cf4a-cdb9-4d14-b6ec-4a0544c178d0

-- Generated from ChapterShannonSampling.lean — solution of BookProof.ChapterShannonSampling.bandSignal_eq_circle_integral
import Mathlib
import Definitions.Def_ChapterShannonSampling
import Theorems.Thm_BookProof_ChapterShannonSampling_half_add_period
import Theorems.Thm_BookProof_ChapterShannonSampling_exists_rep
open BookProof.ChapterShannonSampling




open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

set_option maxHeartbeats 1000000 in
theorem solution (F : AddCircle T → ℂ) (x : ℝ) :
    bandSignal (T := T) F x = ∫ z : AddCircle T, conj (kern (T := T) x z) * F z := by

  have key : (fun z : AddCircle T => conj (kern (T := T) x z) * F z)
      = AddCircle.liftIoc T (-(T / 2)) fun ξ => Complex.exp (2 * π * I * x * ξ) * F ξ := by
    funext z
    obtain ⟨ξ, hξ, rfl⟩ := exists_rep (T := T) z
    rw [kern_coe_apply x hξ, AddCircle.liftIoc_coe_apply hξ, ← Complex.exp_conj]
    congr 2
    simp [Complex.ext_iff]
  rw [key, AddCircle.integral_liftIoc_eq_intervalIntegral, bandSignal, half_add_period]
