-- Prove2me | solution 1 for BookProof.ChapterShannonSampling.bandSignal_hasSum_sinc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:32:34.227056+00:00
-- url     : https://prove2.me/submissions/0324a53a-29d2-4b1f-a581-32bbdc94fafe

-- Generated from ChapterShannonSampling.lean — solution of BookProof.ChapterShannonSampling.bandSignal_hasSum_sinc
import Mathlib
import Definitions.Def_ChapterShannonSampling
import Theorems.Thm_BookProof_ChapterShannonSampling_bandSignal_eq_inner
import Theorems.Thm_BookProof_ChapterShannonSampling_inner_kernLp_fourierBasis
import Theorems.Thm_BookProof_ChapterShannonSampling_bandSignal_sample
open BookProof.ChapterShannonSampling




open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

set_option maxHeartbeats 1000000 in
theorem solution (F : Lp ℂ 2 (haarAddCircle (T := T))) (x : ℝ) :
    HasSum (fun n : ℤ =>
        bandSignal (T := T) (F : AddCircle T → ℂ) (n / T) * (sinc (T * x - n) : ℝ))
      (bandSignal (T := T) (F : AddCircle T → ℂ) x) := by

  have hbase := (fourierBasis (T := T)).hasSum_inner_mul_inner (kernLp (T := T) x) F
  have h2 := hbase.mul_left (T : ℂ)
  rw [← bandSignal_eq_inner] at h2
  have hterm : ∀ n : ℤ, (T : ℂ) * (inner ℂ (kernLp (T := T) x) (fourierBasis (T := T) n)
        * inner ℂ (fourierBasis (T := T) n) F)
      = bandSignal (T := T) (F : AddCircle T → ℂ) (-((n : ℝ) / T)) * (sinc (T * x + n) : ℝ) := by
    intro n
    rw [inner_kernLp_fourierBasis, ← (fourierBasis (T := T)).repr_apply_apply,
      fourierBasis_repr, bandSignal_sample]
    ring
  simp_rw [hterm] at h2
  have h3 := (Equiv.neg ℤ).hasSum_iff.mpr h2
  refine h3.congr_fun fun n => ?_
  simp only [Function.comp_apply, Equiv.neg_apply]
  push_cast
  rw [show -(-(n : ℝ) / T) = (n : ℝ) / T from by ring,
    show T * x + -(n : ℝ) = T * x - n from by ring]
