-- Prove2me | solution 1 for BookProof.BddBelowWallEsa.abs_bumpG_prime_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T11:55:31.266311+00:00
-- url     : https://prove2.me/submissions/54e363ed-1250-44e2-82e6-039dc450b9fa

-- Generated from ChapterBddBelowWallEsa.lean — solution of BookProof.BddBelowWallEsa.abs_bumpG'_le
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallDeficiencyObstruction
import Definitions.Def_ChapterWeakSecondDerivative
import Definitions.Def_ChapterBddBelowWallEsa
open BookProof.BddBelowWallEsa




open MeasureTheory Metric Filter Topology Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction BookProof.WeakSecondDeriv

noncomputable section

set_option maxHeartbeats 1000000 in

theorem solution (x : ℝ) : |bumpG' x| ≤ bumpM := by
  have h := (hasCompactSupport_bumpG'.exists_bound_of_continuous continuous_bumpG').choose_spec x
  simpa [Real.norm_eq_abs, bumpM] using h
