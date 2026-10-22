-- Prove2me | solution 1 for BookProof.BddBelowWallEsa.continuous_zeta_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T11:55:32.48885+00:00
-- url     : https://prove2.me/submissions/dda66ef7-e25b-4e0b-9292-9b35b02f7be2

-- Generated from ChapterBddBelowWallEsa.lean — solution of BookProof.BddBelowWallEsa.continuous_zeta'
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

theorem solution (r : ℝ) : Continuous (zeta' r) :=
  (continuous_bumpG'.comp (continuous_id.div_const r)).div_const r
