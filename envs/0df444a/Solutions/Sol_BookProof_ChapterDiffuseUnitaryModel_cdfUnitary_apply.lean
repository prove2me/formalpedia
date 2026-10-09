-- Prove2me | solution 1 for BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:42:42.743733+00:00
-- url     : https://prove2.me/submissions/e581a2a7-810f-49df-bc13-4eb226b11e56

-- Generated from ChapterDiffuseUnitaryModel.lean — solution of BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_apply
import Mathlib
import Definitions.Def_ChapterDiffuseUnitaryModel
open BookProof.ChapterDiffuseUnitaryModel



noncomputable section

open MeasureTheory ProbabilityTheory Filter


open BookProof.ChapterDiffuseCdfModel BookProof.ChapterLinftyMultiplication

variable (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu]

set_option maxHeartbeats 1000000 in
theorem solution (f : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    cdfUnitary mu f = cdfComp mu f := rfl
