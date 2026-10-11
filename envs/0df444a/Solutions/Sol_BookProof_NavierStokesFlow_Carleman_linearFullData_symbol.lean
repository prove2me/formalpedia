-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.linearFullData_symbol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:07:48.731047+00:00
-- url     : https://prove2.me/submissions/696be3d9-854e-4cee-9f79-60fafa6bbbca

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.linearFullData_symbol
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution : halfLineSymbol linearMode 1 = fun m : ℕ => (m : ℝ) + 1 := by

  funext n
  simp only [halfLineSymbol, halfLineAlpha, linearMode, Fin.sum_univ_three]
  norm_num [nsVelIdx, nsGradIdx, nsLapIdx, Fin.ext_iff]
