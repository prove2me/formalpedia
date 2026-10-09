-- Prove2me | solution 1 for BookProof.ChapterCoherentOccupation.thermalProb_mul_summable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:13:29.421643+00:00
-- url     : https://prove2.me/submissions/0c0a698d-4339-44cf-8956-6283604a5ba2

-- Generated from ChapterCoherentOccupation.lean — solution of BookProof.ChapterCoherentOccupation.thermalProb_mul_summable
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
    Summable (fun n : ℕ => (n : ℝ) * thermalProb nbar n) := by

  have hr := norm_thermalRatio_lt_one h
  have h1 : Summable (fun n : ℕ => (n : ℝ) * thermalRatio nbar ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  exact (h1.mul_left (1 / (nbar + 1))).congr fun n => by rw [thermalProb]; ring
