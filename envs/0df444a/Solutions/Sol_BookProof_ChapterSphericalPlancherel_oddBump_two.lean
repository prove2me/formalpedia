-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.oddBump_two
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:05.262986+00:00
-- url     : https://prove2.me/submissions/243d39b7-1df3-4e1a-8fd0-b5528d09925a

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.oddBump_two
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution : oddBump 2 = 1 := by

  have h1 : bumpAtTwo (2 : ℝ) = 1 := bumpAtTwo.one_of_mem_closedBall (by simp [bumpAtTwo])
  have h2 : bumpAtTwo (-2 : ℝ) = 0 := by
    apply ContDiffBump.zero_of_le_dist
    simp [bumpAtTwo, Real.dist_eq]
    norm_num
  simp [oddBump, h1, h2]
