-- Prove2me | solution 1 for BookProof.ChapterCoherentFidelity.neg_log_fidelityC
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:09:36.046455+00:00
-- url     : https://prove2.me/submissions/24e1ddf4-dcd2-48c3-be94-2e3195fffb52

-- Generated from ChapterCoherentFidelity.lean — solution of BookProof.ChapterCoherentFidelity.neg_log_fidelityC
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
theorem solution (q k : EuclideanSpace ℂ (Fin n)) :
    -Real.log (fidelityC q k) = ‖q - k‖ ^ 2 := by

  rw [fidelityC_eq_exp_neg_dist_sq, Real.log_exp, neg_neg]
