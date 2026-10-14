-- Prove2me | solution 1 for BookProof.ChapterCoherentGeometry.bornWeight_max_of_nearest
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:57:17.655314+00:00
-- url     : https://prove2.me/submissions/532e6a0f-2c88-4626-af49-fc3564a49724

-- Generated from ChapterCoherentGeometry.lean — solution of BookProof.ChapterCoherentGeometry.bornWeight_max_of_nearest
import Mathlib
import Definitions.Def_ChapterCoherentGeometry
import Theorems.Thm_BookProof_ChapterCoherentGeometry_bornWeight_le_iff_dist_le
import Definitions.Def_ChapterCoherentOverlap
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterCoherentGeometry



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m)
    (hj : ∀ l, ‖q - k j‖ ≤ ‖q - k l‖) (i : Fin m) :
    bornWeight q k i ≤ bornWeight q k j := (bornWeight_le_iff_dist_le q k i j).2 (hj i)
