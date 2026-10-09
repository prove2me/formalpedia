-- Prove2me | solution 1 for BookProof.ChapterBoseEinstein.thermalRatio_boseEinstein
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:32:58.69885+00:00
-- url     : https://prove2.me/submissions/7c5ed34c-50fc-49a2-b070-ec1cdfe6ba4e

-- Generated from ChapterBoseEinstein.lean — solution of BookProof.ChapterBoseEinstein.thermalRatio_boseEinstein
import Mathlib
import Definitions.Def_ChapterBoseEinstein
import Theorems.Thm_BookProof_ChapterBoseEinstein_exp_sub_one_pos
open BookProof.ChapterBoseEinstein



noncomputable section

open Filter Topology


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation

variable {x : ℝ}

variable {x : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hx : 0 < x) :
    thermalRatio (boseEinstein x) = Real.exp (-x) := by

  have h := exp_sub_one_pos hx
  have he : (0 : ℝ) < Real.exp x := Real.exp_pos _
  rw [thermalRatio, boseEinstein, Real.exp_neg]
  field_simp
  ring
