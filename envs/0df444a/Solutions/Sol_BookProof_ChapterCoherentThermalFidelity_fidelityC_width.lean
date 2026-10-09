-- Prove2me | solution 1 for BookProof.ChapterCoherentThermalFidelity.fidelityC_width
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:36:22.614112+00:00
-- url     : https://prove2.me/submissions/2bdab164-1be0-4c59-90ba-4d9e3947c100

-- Generated from ChapterCoherentThermalFidelity.lean — solution of BookProof.ChapterCoherentThermalFidelity.fidelityC_width
import Mathlib
import Definitions.Def_ChapterCoherentThermalFidelity
import Theorems.Thm_BookProof_ChapterCoherentFidelity_fidelityC_eq_exp_neg_dist_sq
open BookProof.ChapterCoherentThermalFidelity



noncomputable section


open BookProof.ChapterCoherentOccupation BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentFidelity BookProof.ChapterDisplacedThermalOverlap
open Real

variable {nbar lam : ℝ}

variable {nbar lam : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (q k : EuclideanSpace ℂ (Fin n)) :
    fidelityC q k = Real.exp (-(‖q - k‖ ^ 2 / (coherentWidth + coherentWidth))) := by

  rw [fidelityC_eq_exp_neg_dist_sq, coherentWidth]
  norm_num
