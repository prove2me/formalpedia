-- Prove2me | solution 1 for BookProof.ChapterCoherentGeometry.bornWeight_le_iff_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:37:07.077395+00:00
-- url     : https://prove2.me/submissions/b7409e67-5d8d-4ad3-abf7-111fdf37020e

-- Generated from ChapterCoherentGeometry.lean — solution of BookProof.ChapterCoherentGeometry.bornWeight_le_iff_dist_le
import Mathlib
import Definitions.Def_ChapterCoherentGeometry
import Theorems.Thm_BookProof_ChapterCoherentGeometry_coherentOverlap_le_iff_dist_le
import Theorems.Thm_BookProof_ChapterCoherentOverlap_coherentOverlap_pos
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_bornDenom_pos
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
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (i j : Fin m) :
    bornWeight q k i ≤ bornWeight q k j ↔ ‖q - k j‖ ≤ ‖q - k i‖ := by

  have hden : 0 < ∑ l, bornNumer q (k l) := bornDenom_pos q k i
  have hi := coherentOverlap_pos q (k i)
  have hj := coherentOverlap_pos q (k j)
  rw [bornWeight, bornWeight, div_le_div_iff_of_pos_right hden, bornNumer, bornNumer]
  constructor
  · intro h
    exact (coherentOverlap_le_iff_dist_le q (k i) (k j)).1 (by nlinarith)
  · intro h
    have := (coherentOverlap_le_iff_dist_le q (k i) (k j)).2 h
    nlinarith
