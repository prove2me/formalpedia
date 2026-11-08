-- Prove2me | solution 1 for BookProof.CarlemanSimplex.sBd_subset_simplexF
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:05:51.918246+00:00
-- url     : https://prove2.me/submissions/58953608-e0d8-4e86-bbab-27554787d79b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.sBd_subset_simplexF
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_mem_simplexF
import Theorems.Thm_BookProof_CarlemanSimplex_mem_sBd
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanSimplex




open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (d N k : ℕ) : sBd d N k ⊆ simplexF d N := by

  intro a ha
  rw [mem_sBd] at ha
  exact mem_simplexF.mpr ha.1
