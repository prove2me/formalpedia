-- Prove2me | solution 1 for BookProof.ChapterCoherentOccupation.thermalProb_summable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:13:16.167275+00:00
-- url     : https://prove2.me/submissions/686297b8-0d9d-455c-a1aa-cdad29537c4b

-- Generated from ChapterCoherentOccupation.lean — solution of BookProof.ChapterCoherentOccupation.thermalProb_summable
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Theorems.Thm_BookProof_ChapterCoherentTemperature_norm_thermalRatio_lt_one
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentOccupation



noncomputable section


open Real Nat ProbabilityTheory

set_option maxHeartbeats 1000000 in
theorem solution {nbar : ℝ} (h : 0 ≤ nbar) :
    Summable (fun n : ℕ => thermalProb nbar n) := by

  have hr := norm_thermalRatio_lt_one h
  have hgeom : Summable (fun n : ℕ => thermalRatio nbar ^ n) :=
    summable_geometric_of_norm_lt_one hr
  exact (hgeom.mul_left (1 / (nbar + 1))).congr fun n => by rw [thermalProb]
