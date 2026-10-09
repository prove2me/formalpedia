-- Prove2me | solution 1 for BookProof.ChapterBoseEinstein.thermalProb_boseEinstein
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:32:59.968198+00:00
-- url     : https://prove2.me/submissions/26a91053-bde5-406c-8a67-ea14debd8704

-- Generated from ChapterBoseEinstein.lean — solution of BookProof.ChapterBoseEinstein.thermalProb_boseEinstein
import Mathlib
import Definitions.Def_ChapterBoseEinstein
import Theorems.Thm_BookProof_ChapterBoseEinstein_exp_sub_one_pos
import Theorems.Thm_BookProof_ChapterBoseEinstein_thermalRatio_boseEinstein
open BookProof.ChapterBoseEinstein



noncomputable section

open Filter Topology


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation

variable {x : ℝ}

variable {x : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hx : 0 < x) (n : ℕ) :
    thermalProb (boseEinstein x) n = (1 - Real.exp (-x)) * Real.exp (-x) ^ n := by

  have h := exp_sub_one_pos hx
  have he : (0 : ℝ) < Real.exp x := Real.exp_pos _
  rw [thermalProb, thermalRatio_boseEinstein hx, boseEinstein, Real.exp_neg]
  congr 1
  field_simp
  ring
