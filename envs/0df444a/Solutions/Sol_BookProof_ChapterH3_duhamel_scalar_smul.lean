-- Prove2me | solution 1 for BookProof.ChapterH3.duhamel_scalar_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:34:43.882077+00:00
-- url     : https://prove2.me/submissions/21ac765f-94e3-4cb1-a7d8-003ada8bab23

-- Generated from ChapterH3.lean — solution of BookProof.ChapterH3.duhamel_scalar_smul
import Mathlib
import Definitions.Def_ChapterH3
import Theorems.Thm_BookProof_ChapterH3_duhamel_scalar
import Definitions.Def_ChapterH1
open BookProof.ChapterH3



open scoped BigOperators
open intervalIntegral
open BookProof.ChapterH1


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (z g : ℂ) (δ : ℝ) :
    (∫ s in (0:ℝ)..δ, Complex.exp ((↑(δ - s)) * z) * g)
      = δ * BookProof.ChapterH1.phi 1 (δ * z) * g := by

  rw [intervalIntegral.integral_mul_const, duhamel_scalar]
