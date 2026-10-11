-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.oddBump_odd
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:03.946788+00:00
-- url     : https://prove2.me/submissions/566db740-d00e-4413-bf53-216eec5833e3

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.oddBump_odd
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (x : ℝ) : oddBump (-x) = -oddBump x := by

  simp only [oddBump, neg_neg]
  ring
