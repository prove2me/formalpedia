-- Prove2me | solution 1 for BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:35:13.569208+00:00
-- url     : https://prove2.me/submissions/1b55fd61-4d98-4780-a44b-d9cdc62c55da

-- Generated from ChapterCoherentThermalFidelity.lean — solution of BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_hasSum
import Mathlib
import Definitions.Def_ChapterCoherentThermalFidelity
import Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_eq
import Theorems.Thm_BookProof_ChapterCoherentOccupation_hasSum_expSeries
open BookProof.ChapterCoherentThermalFidelity



noncomputable section


open BookProof.ChapterCoherentOccupation BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentFidelity BookProof.ChapterDisplacedThermalOverlap
open Real

variable {nbar lam : ℝ}

variable {nbar lam : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 ≤ nbar) (lam : ℝ) :
    HasSum (fun n : ℕ => coherentOccupation lam n * thermalProb nbar n)
      (Real.exp (-(lam / (nbar + 1))) / (nbar + 1)) := by

  have hpos : (0 : ℝ) < nbar + 1 := by linarith
  have hkey := (hasSum_expSeries (lam * thermalRatio nbar)).mul_left
    (Real.exp (-lam) * (1 / (nbar + 1)))
  have hval : Real.exp (-lam) * (1 / (nbar + 1)) * Real.exp (lam * thermalRatio nbar)
      = Real.exp (-(lam / (nbar + 1))) / (nbar + 1) := by
    rw [mul_comm (Real.exp (-lam)) (1 / (nbar + 1)), mul_assoc, ← Real.exp_add]
    rw [thermalRatio]
    rw [show -lam + lam * (nbar / (nbar + 1)) = -(lam / (nbar + 1)) by
      field_simp; ring]
    ring
  rw [hval] at hkey
  refine hkey.congr_fun fun n => ?_
  rw [coherentOccupation_eq, thermalProb, mul_pow]
  ring
