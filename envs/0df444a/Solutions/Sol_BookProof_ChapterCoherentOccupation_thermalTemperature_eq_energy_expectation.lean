-- Prove2me | solution 1 for BookProof.ChapterCoherentOccupation.thermalTemperature_eq_energy_expectation
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:13:43.778439+00:00
-- url     : https://prove2.me/submissions/a1632aef-11c9-4f98-9cfc-a57f9f50ce10

-- Generated from ChapterCoherentOccupation.lean — solution of BookProof.ChapterCoherentOccupation.thermalTemperature_eq_energy_expectation
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Theorems.Thm_BookProof_ChapterCoherentOccupation_thermalOccupation_energy
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentOccupation



noncomputable section


open Real Nat ProbabilityTheory

set_option maxHeartbeats 1000000 in
theorem solution {nbar : ℝ} (h : 0 ≤ nbar) :
    thermalTemperature nbar = ∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb nbar n := by

  rw [thermalOccupation_energy h, thermalTemperature]
