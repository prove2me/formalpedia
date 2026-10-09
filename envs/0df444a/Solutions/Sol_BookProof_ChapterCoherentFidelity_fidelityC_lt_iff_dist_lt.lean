-- Prove2me | solution 1 for BookProof.ChapterCoherentFidelity.fidelityC_lt_iff_dist_lt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:09:34.968977+00:00
-- url     : https://prove2.me/submissions/a8dc8f52-9299-4530-b584-48e9bf15a909

-- Generated from ChapterCoherentFidelity.lean — solution of BookProof.ChapterCoherentFidelity.fidelityC_lt_iff_dist_lt
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
import Theorems.Thm_BookProof_ChapterCoherentFidelity_fidelityC_le_iff_dist_le
open BookProof.ChapterCoherentFidelity



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k k' : EuclideanSpace ℂ (Fin n)) :
    fidelityC q k < fidelityC q k' ↔ ‖q - k'‖ < ‖q - k‖ := by

  rw [← not_le, ← not_le, fidelityC_le_iff_dist_le]
