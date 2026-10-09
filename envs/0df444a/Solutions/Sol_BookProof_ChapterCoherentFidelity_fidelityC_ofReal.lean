-- Prove2me | solution 1 for BookProof.ChapterCoherentFidelity.fidelityC_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:10:17.444412+00:00
-- url     : https://prove2.me/submissions/545b64a9-e4b7-42ab-8f0b-704653089194

-- Generated from ChapterCoherentFidelity.lean — solution of BookProof.ChapterCoherentFidelity.fidelityC_ofReal
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
import Theorems.Thm_BookProof_ChapterCoherentFidelity_fidelityC_eq_bornNumerC
import Theorems.Thm_BookProof_ChapterCoherentGeometry_bornNumer_eq_exp_neg_dist_sq
import Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_bornNumerC_ofReal
open BookProof.ChapterCoherentFidelity



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℝ (Fin n)) :
    fidelityC (ofRealVec q) (ofRealVec k) = Real.exp (-‖q - k‖ ^ 2) := by

  rw [fidelityC_eq_bornNumerC, bornNumerC_ofReal,
    BookProof.ChapterCoherentGeometry.bornNumer_eq_exp_neg_dist_sq]
