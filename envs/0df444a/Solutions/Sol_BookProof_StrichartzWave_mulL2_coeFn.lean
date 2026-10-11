-- Prove2me | solution 1 for BookProof.StrichartzWave.mulL2_coeFn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:25:56.281536+00:00
-- url     : https://prove2.me/submissions/25700cc0-96af-4bbf-aa0f-0b8a28a92bef

-- Generated from ChapterWaveBoundedPotential.lean — solution of BookProof.StrichartzWave.mulL2_coeFn
import Mathlib
import Definitions.Def_ChapterWaveBoundedPotential
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (W : Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V))
    (u : Lp ℂ 2 (volume : Measure V)) :
    (mulL2 W u : V → ℂ) =ᵐ[(volume : Measure V)] fun x => (W x) * (u x) := ContinuousLinearMap.coeFn_holder _ _ _
