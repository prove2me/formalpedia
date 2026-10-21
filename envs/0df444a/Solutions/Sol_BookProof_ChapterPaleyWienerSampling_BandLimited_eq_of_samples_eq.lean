-- Prove2me | solution 1 for BookProof.ChapterPaleyWienerSampling.BandLimited.eq_of_samples_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T16:41:22.917286+00:00
-- url     : https://prove2.me/submissions/5ad97e29-c834-4ec4-8329-f064c82d4bff

-- Generated from ChapterPaleyWienerSampling.lean — solution of BookProof.ChapterPaleyWienerSampling.BandLimited.eq_of_samples_eq
import Mathlib
import Definitions.Def_ChapterPaleyWienerSampling
import Theorems.Thm_BookProof_ChapterPaleyWienerSampling_BandLimited_hasSum_sinc
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
theorem solution (hf : BandLimited T f) (hg : BandLimited T g)
    (h : ∀ n : ℤ, f ((n : ℝ) / T) = g ((n : ℝ) / T)) : f = g := by

  funext x
  refine HasSum.unique (hf.hasSum_sinc x) ?_
  refine (hg.hasSum_sinc x).congr_fun fun n => ?_
  rw [h n]
