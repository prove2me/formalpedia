-- Prove2me | solution 1 for BookProof.ChapterBoseEinstein.boseEinstein_strictAntiOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:33:02.697326+00:00
-- url     : https://prove2.me/submissions/fc1ef3b1-b387-47d7-a334-8147959d08ad

-- Generated from ChapterBoseEinstein.lean — solution of BookProof.ChapterBoseEinstein.boseEinstein_strictAntiOn
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
theorem solution : StrictAntiOn boseEinstein (Set.Ioi 0) := by

  intro a ha b _ hab
  have ha' : 0 < a := ha
  have h1 := exp_sub_one_pos ha'
  have hexp : Real.exp a < Real.exp b := Real.exp_lt_exp.mpr hab
  rw [boseEinstein, boseEinstein]
  apply one_div_lt_one_div_of_lt h1
  linarith
