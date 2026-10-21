-- Prove2me | solution 1 for BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal_lp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T16:41:20.416219+00:00
-- url     : https://prove2.me/submissions/329505b5-8f11-48e1-89d6-7e7c6786cbeb

-- Generated from ChapterPaleyWienerSampling.lean — solution of BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal_lp
import Mathlib
import Definitions.Def_ChapterPaleyWienerSampling
import Theorems.Thm_BookProof_ChapterPaleyWienerSampling_bandSignal_bandSpectrumLp
import Theorems.Thm_BookProof_ChapterPaleyWienerSampling_BandLimited_eq_bandSignal
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
    f x = bandSignal (T := T) ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) :
      AddCircle T → ℂ) x := by

  rw [bandSignal_bandSpectrumLp hf x, hf.eq_bandSignal x]
