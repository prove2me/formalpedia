-- Prove2me | solution 1 for BookProof.ChapterLpScaleMeasure.memLp_top_smul_measure_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:26:41.091087+00:00
-- url     : https://prove2.me/submissions/1d91eccd-5566-42df-bcf9-9ed1855af5bf

-- Generated from ChapterLpScaleMeasure.lean — solution of BookProof.ChapterLpScaleMeasure.memLp_top_smul_measure_iff
import Mathlib
import Definitions.Def_ChapterLpScaleMeasure
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLpScaleMeasure



noncomputable section

open MeasureTheory ENNReal


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {nu : Measure α} {c : ENNReal}

variable {α : Type*} [MeasurableSpace α] {nu : Measure α} {c : ENNReal}

set_option maxHeartbeats 1000000 in
theorem solution (hc0 : c ≠ 0) {f : α → ℂ} :
    MemLp f ⊤ (c • nu) ↔ MemLp f ⊤ nu := by

  constructor
  · rintro ⟨hm, hlt⟩
    refine ⟨(aestronglyMeasurable_smul_measure_iff hc0).1 hm, ?_⟩
    rwa [eLpNorm_exponent_top, eLpNormEssSup_ennreal_smul_measure hc0] at hlt
  · rintro ⟨hm, hlt⟩
    refine ⟨(aestronglyMeasurable_smul_measure_iff hc0).2 hm, ?_⟩
    rwa [eLpNorm_exponent_top, eLpNormEssSup_ennreal_smul_measure hc0]
