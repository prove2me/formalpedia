-- Prove2me | solution 1 for BookProof.MixedLinearEsa.norm_gaugeFun
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T22:00:40.831991+00:00
-- url     : https://prove2.me/submissions/68a73171-134b-4e34-b540-8d57c73ba744

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.norm_gaugeFun
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterFarisLavine
open BookProof.MixedLinearEsa




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (b m : V) (x : V) : ‖gaugeFun b m x‖ = 1 := by

  rw [gaugeFun, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _
