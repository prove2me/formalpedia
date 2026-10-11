-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.summable_normSq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:05:57.917048+00:00
-- url     : https://prove2.me/submissions/dd12aff0-3ec9-48e6-8f6d-76369a0d4e93

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.summable_normSq
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution (f : L2N) : Summable fun n : ℕ => ‖(f : ℕ → ℂ) n‖ ^ 2 := by

  have hsum := (lp.memℓp f).summable (p := 2) (by norm_num)
  simpa [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast] using hsum
