-- Prove2me | solution 1 for BookProof.ChapterShannonSampling.continuous_bandSignal_lp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:32:37.010203+00:00
-- url     : https://prove2.me/submissions/4d46f633-2229-4e13-8a87-ad7288626e42

-- Generated from ChapterShannonSampling.lean — solution of BookProof.ChapterShannonSampling.continuous_bandSignal_lp
import Mathlib
import Definitions.Def_ChapterShannonSampling
import Theorems.Thm_BookProof_ChapterShannonSampling_integrableOn_spectrum
import Theorems.Thm_BookProof_ChapterShannonSampling_continuous_bandSignal
open BookProof.ChapterShannonSampling




open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

set_option maxHeartbeats 1000000 in
theorem solution (F : Lp ℂ 2 (haarAddCircle (T := T))) :
    Continuous (bandSignal (T := T) (F : AddCircle T → ℂ)) := continuous_bandSignal _ (integrableOn_spectrum F)
