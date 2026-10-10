-- Prove2me | solution 1 for BookProof.MixedLinearEsa.hasTemperateGrowth_polyPotential
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T22:03:33.989927+00:00
-- url     : https://prove2.me/submissions/3d48f75d-5227-4e1b-9f26-3b4dfd20dca0

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.hasTemperateGrowth_polyPotential
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
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem solution (c : ℕ → ℝ) (n : ℕ) (m : V) :
    Function.HasTemperateGrowth (polyPotential c n m) := by

  unfold polyPotential
  refine Function.HasTemperateGrowth.sum fun i _ => ?_
  exact (Function.HasTemperateGrowth.const (c i)).mul
    ((Function.hasTemperateGrowth_inner_left m).pow i)
