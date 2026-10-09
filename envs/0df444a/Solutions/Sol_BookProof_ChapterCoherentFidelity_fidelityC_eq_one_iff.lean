-- Prove2me | solution 1 for BookProof.ChapterCoherentFidelity.fidelityC_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:09:07.054736+00:00
-- url     : https://prove2.me/submissions/49a21c5a-0905-4a5b-bca8-0fc027ad0fd7

-- Generated from ChapterCoherentFidelity.lean — solution of BookProof.ChapterCoherentFidelity.fidelityC_eq_one_iff
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
    fidelityC q k = 1 ↔ q = k := by

  rw [fidelityC_eq_exp_neg_dist_sq, Real.exp_eq_one_iff, neg_eq_zero,
    pow_eq_zero_iff (two_ne_zero), norm_eq_zero, sub_eq_zero]
