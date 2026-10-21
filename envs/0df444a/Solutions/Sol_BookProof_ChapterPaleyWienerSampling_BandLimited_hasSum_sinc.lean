-- Prove2me | solution 1 for BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sinc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T16:55:16.901143+00:00
-- url     : https://prove2.me/submissions/ca4122c0-1002-4ecd-9eab-d4d987ba3655

-- Generated from ChapterPaleyWienerSampling.lean — solution of BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sinc
import Mathlib
import Definitions.Def_ChapterPaleyWienerSampling
import Theorems.Thm_BookProof_ChapterPaleyWienerSampling_BandLimited_eq_bandSignal_lp
import Theorems.Thm_BookProof_ChapterShannonSampling_bandSignal_hasSum_sinc
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterPaleyWienerSampling
open BookProof.ChapterPaleyWienerSampling.BandLimited




open MeasureTheory Complex AddCircle Set
open scoped Real FourierTransform
open BookProof.ChapterShannonSampling (sinc bandSignal exists_rep half_add_period)
open BookProof.ChapterShannonSampling

variable {T : ℝ} {f g : ℝ → ℂ}
variable {T : ℝ} [hT : Fact (0 < T)] {f g : ℝ → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution (hf : BandLimited T f) (x : ℝ) :
    HasSum (fun n : ℤ => f ((n : ℝ) / T) * (sinc (T * x - n) : ℝ)) (f x) := by

  have hbase := bandSignal_hasSum_sinc (bandSpectrumLp hf) x
  rw [← hf.eq_bandSignal_lp x] at hbase
  refine hbase.congr_fun fun n => ?_
  rw [hf.eq_bandSignal_lp ((n : ℝ) / T)]
