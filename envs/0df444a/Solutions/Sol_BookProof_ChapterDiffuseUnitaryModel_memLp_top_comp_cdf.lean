-- Prove2me | solution 1 for BookProof.ChapterDiffuseUnitaryModel.memLp_top_comp_cdf
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:42:58.670327+00:00
-- url     : https://prove2.me/submissions/86528650-a952-4177-8341-2fffe9227bb1

-- Generated from ChapterDiffuseUnitaryModel.lean — solution of BookProof.ChapterDiffuseUnitaryModel.memLp_top_comp_cdf
import Mathlib
import Definitions.Def_ChapterDiffuseUnitaryModel
open BookProof.ChapterDiffuseUnitaryModel



noncomputable section

open MeasureTheory ProbabilityTheory Filter


open BookProof.ChapterDiffuseCdfModel BookProof.ChapterLinftyMultiplication

variable (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu]

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℂ}
    (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    MemLp (fun x => g (cdf mu x)) ⊤ mu := hg.comp_measurePreserving (measurePreserving_cdf mu)
