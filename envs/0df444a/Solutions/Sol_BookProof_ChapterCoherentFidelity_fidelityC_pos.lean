-- Prove2me | solution 1 for BookProof.ChapterCoherentFidelity.fidelityC_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:08:49.478656+00:00
-- url     : https://prove2.me/submissions/e4c8af79-87ac-4f78-8cd1-b2389d76c74c

-- Generated from ChapterCoherentFidelity.lean — solution of BookProof.ChapterCoherentFidelity.fidelityC_pos
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
import Theorems.Thm_BookProof_ChapterCoherentFidelity_fidelityC_eq_exp_neg_dist_sq
open BookProof.ChapterCoherentFidelity



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℂ (Fin n)) : 0 < fidelityC q k := by

  rw [fidelityC_eq_exp_neg_dist_sq]; exact Real.exp_pos _
