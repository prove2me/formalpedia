-- Prove2me | solution 1 for BookProof.ChapterPaleyWienerSampling.BandLimited.integrable_fourier
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T16:41:15.142983+00:00
-- url     : https://prove2.me/submissions/1c0608ba-8a9f-460b-a26b-ffbc14675418

-- Generated from ChapterPaleyWienerSampling.lean — solution of BookProof.ChapterPaleyWienerSampling.BandLimited.integrable_fourier
import Mathlib
import Definitions.Def_ChapterPaleyWienerSampling
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterPaleyWienerSampling
open BookProof.ChapterPaleyWienerSampling.BandLimited




open MeasureTheory Complex AddCircle Set
open scoped Real FourierTransform
open BookProof.ChapterShannonSampling (sinc bandSignal exists_rep half_add_period)

variable {T : ℝ} {f g : ℝ → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution (hf : BandLimited T f) : Integrable (𝓕 f) := hf.continuous_fourier.integrable_of_hasCompactSupport hf.hasCompactSupport_fourier
