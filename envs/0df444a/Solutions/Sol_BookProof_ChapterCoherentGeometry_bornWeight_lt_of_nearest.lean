-- Prove2me | solution 1 for BookProof.ChapterCoherentGeometry.bornWeight_lt_of_nearest
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:57:18.754978+00:00
-- url     : https://prove2.me/submissions/ecd7069a-ed8a-481c-a473-d6d0a7cddf58

-- Generated from ChapterCoherentGeometry.lean — solution of BookProof.ChapterCoherentGeometry.bornWeight_lt_of_nearest
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
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (i j : Fin m)
    (hij : ‖q - k j‖ < ‖q - k i‖) :
    bornWeight q k i < bornWeight q k j := by

  rw [← not_le, bornWeight_le_iff_dist_le]
  exact not_le.2 hij
