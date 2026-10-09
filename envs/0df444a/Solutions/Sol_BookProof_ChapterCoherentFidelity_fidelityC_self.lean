-- Prove2me | solution 1 for BookProof.ChapterCoherentFidelity.fidelityC_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:09:04.759013+00:00
-- url     : https://prove2.me/submissions/b18bdf9d-63f7-49a6-8ed2-702af075593b

-- Generated from ChapterCoherentFidelity.lean — solution of BookProof.ChapterCoherentFidelity.fidelityC_self
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
theorem solution (q : EuclideanSpace ℂ (Fin n)) : fidelityC q q = 1 := by

  rw [fidelityC_eq_exp_neg_dist_sq]
  simp
