-- Prove2me | solution 1 for BookProof.ChapterShannonSampling.bandSignal_eq_of_samples_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:32:53.753599+00:00
-- url     : https://prove2.me/submissions/d91a72a4-412d-49d2-81e3-b7612dc9495d

-- Generated from ChapterShannonSampling.lean — solution of BookProof.ChapterShannonSampling.bandSignal_eq_of_samples_eq
import Mathlib
import Definitions.Def_ChapterShannonSampling
import Theorems.Thm_BookProof_ChapterShannonSampling_bandSignal_hasSum_sinc
open BookProof.ChapterShannonSampling




open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

set_option maxHeartbeats 1000000 in
theorem solution (F G : Lp ℂ 2 (haarAddCircle (T := T)))
    (h : ∀ n : ℤ, bandSignal (T := T) (F : AddCircle T → ℂ) (n / T)
      = bandSignal (T := T) (G : AddCircle T → ℂ) (n / T)) (x : ℝ) :
    bandSignal (T := T) (F : AddCircle T → ℂ) x
      = bandSignal (T := T) (G : AddCircle T → ℂ) x := by

  refine HasSum.unique (bandSignal_hasSum_sinc F x) ?_
  refine (bandSignal_hasSum_sinc G x).congr_fun fun n => ?_
  rw [h n]
