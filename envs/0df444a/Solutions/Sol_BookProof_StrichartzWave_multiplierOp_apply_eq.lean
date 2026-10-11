-- Prove2me | solution 1 for BookProof.StrichartzWave.multiplierOp_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:27:37.561073+00:00
-- url     : https://prove2.me/submissions/ae664751-97f7-4978-bc7b-d2335abf1096

-- Generated from ChapterWaveUnboundedPotential.lean — solution of BookProof.StrichartzWave.multiplierOp_apply_eq
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (m : V → ℝ) (f : 𝓢(V, ℂ)) :
    (multiplierOp m f : 𝓢(V, ℂ)) = 𝓕⁻ (potentialOp m (𝓕 f : 𝓢(V, ℂ))) := rfl
