-- Prove2me | solution 1 for BookProof.ChapterObservableOperator.bornProb_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:51.310738+00:00
-- url     : https://prove2.me/submissions/a30724b9-24ff-4a58-88f4-a29d16d4bf1e

-- Generated from ChapterObservableOperator.lean — solution of BookProof.ChapterObservableOperator.bornProb_sum_one
import Mathlib
import Definitions.Def_ChapterObservableOperator
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterObservableOperator



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin n)))
    (q : EuclideanSpace ℂ (Fin n)) (hq : ‖q‖ = 1) :
    ∑ j, bornProb (fun j => b j) q j = 1 := by

  simpa [bornProb, hq] using b.sum_sq_norm_inner_right q
