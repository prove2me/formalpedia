-- Prove2me | solution 1 for BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:35:14.819369+00:00
-- url     : https://prove2.me/submissions/398831be-873f-4c81-9ee0-0721b7f5b8d7

-- Generated from ChapterCoherentThermalFidelity.lean — solution of BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq
import Mathlib
import Definitions.Def_ChapterCoherentThermalFidelity
import Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_coherentThermalFidelity_hasSum
open BookProof.ChapterCoherentThermalFidelity



noncomputable section


open BookProof.ChapterCoherentOccupation BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentFidelity BookProof.ChapterDisplacedThermalOverlap
open Real

variable {nbar lam : ℝ}

variable {nbar lam : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 ≤ nbar) (lam : ℝ) :
    coherentThermalFidelity nbar lam = Real.exp (-(lam / (nbar + 1))) / (nbar + 1) := (coherentThermalFidelity_hasSum h lam).tsum_eq
