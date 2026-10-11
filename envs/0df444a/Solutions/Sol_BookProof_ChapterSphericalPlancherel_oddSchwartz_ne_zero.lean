-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.oddSchwartz_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:09.755425+00:00
-- url     : https://prove2.me/submissions/7f7a4e2d-1fe2-4b62-a100-7a6a94a44fdf

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.oddSchwartz_ne_zero
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Theorems.Thm_BookProof_ChapterSphericalPlancherel_oddBump_two
import Theorems.Thm_BookProof_ChapterSphericalPlancherel_oddSchwartz_apply
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution : oddSchwartz ≠ 0 := by

  intro h
  have h2 : oddSchwartz 2 = 0 := by rw [h]; rfl
  rw [oddSchwartz_apply, oddBump_two] at h2
  exact one_ne_zero h2
