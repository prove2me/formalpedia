-- Prove2me | solution 1 for BookProof.StrichartzWave.hasTemperateGrowth_symbolFn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:27:54.343988+00:00
-- url     : https://prove2.me/submissions/7c6b2849-5667-4122-a7b3-afd82bd910ca

-- Generated from ChapterWaveUnboundedPotential.lean — solution of BookProof.StrichartzWave.hasTemperateGrowth_symbolFn
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem solution (c : ι → ℝ) (w : ι → V) (κ : ℝ) :
    Function.HasTemperateGrowth (symbolFn c w κ) := by

  refine Function.HasTemperateGrowth.add
    (Function.HasTemperateGrowth.sum fun i _ => ?_) (Function.HasTemperateGrowth.const κ)
  exact (Function.HasTemperateGrowth.const (c i * (-4 * Real.pi ^ 2))).mul
    ((Function.hasTemperateGrowth_inner_left (w i)).pow 2)
