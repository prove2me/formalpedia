-- Prove2me | solution 1 for BookProof.ChapterShannonSampling.bandSignal_eq_inner
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:32:31.140977+00:00
-- url     : https://prove2.me/submissions/62efac4e-240c-4f3b-91c2-086f2d6801c8

-- Generated from ChapterShannonSampling.lean — solution of BookProof.ChapterShannonSampling.bandSignal_eq_inner
import Mathlib
import Definitions.Def_ChapterShannonSampling
import Theorems.Thm_BookProof_ChapterShannonSampling_bandSignal_eq_circle_integral
import Theorems.Thm_BookProof_ChapterShannonSampling_integral_haar_eq
import Theorems.Thm_BookProof_ChapterShannonSampling_inner_kernLp_apply
open BookProof.ChapterShannonSampling




open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

set_option maxHeartbeats 1000000 in
theorem solution (F : Lp ℂ 2 (haarAddCircle (T := T))) (x : ℝ) :
    bandSignal (T := T) (F : AddCircle T → ℂ) x
      = (T : ℂ) * inner ℂ (kernLp (T := T) x) F := by

  rw [inner_kernLp_apply, integral_haar_eq, bandSignal_eq_circle_integral,
    ← AddCircle.intervalIntegral_preimage T (-(T / 2))]
