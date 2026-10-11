-- Prove2me | solution 1 for BookProof.ChapterSternGerlach.dft_geom_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:59:42.393995+00:00
-- url     : https://prove2.me/submissions/8b24d0ec-4a2f-42db-a702-ac6ecc50d2b6

-- Generated from ChapterSternGerlach.lean — solution of BookProof.ChapterSternGerlach.dft_geom_sum_zero
import Mathlib
import Definitions.Def_ChapterSternGerlach
open BookProof.ChapterSternGerlach




open Complex Matrix Finset

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (w : ℂ) (hw : w ≠ 1) (hwn : w ^ n = 1) :
    ∑ i ∈ Finset.range n, w ^ i = 0 := by

  rw [geom_sum_eq hw, hwn]; simp
