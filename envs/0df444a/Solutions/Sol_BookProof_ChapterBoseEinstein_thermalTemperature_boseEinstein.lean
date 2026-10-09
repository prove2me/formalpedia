-- Prove2me | solution 1 for BookProof.ChapterBoseEinstein.thermalTemperature_boseEinstein
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:33:04.149494+00:00
-- url     : https://prove2.me/submissions/107c2b16-1ced-40d0-8fd8-4016cdeb5403

-- Generated from ChapterBoseEinstein.lean — solution of BookProof.ChapterBoseEinstein.thermalTemperature_boseEinstein
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
    thermalTemperature (boseEinstein x) = (Real.exp x + 1) / (2 * (Real.exp x - 1)) := by

  have h := exp_sub_one_pos hx
  rw [thermalTemperature, boseEinstein]
  field_simp
  ring
