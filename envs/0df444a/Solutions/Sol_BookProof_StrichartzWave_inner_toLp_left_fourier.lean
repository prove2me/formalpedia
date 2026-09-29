-- Prove2me | solution 1 for BookProof.StrichartzWave.inner_toLp_left_fourier
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:36:55.354806+00:00
-- url     : https://prove2.me/submissions/a68f6aaf-fc52-46f3-b9b3-f53b3d35db44

-- Generated from ChapterStrichartzWave.lean — solution of BookProof.StrichartzWave.inner_toLp_left_fourier
import Mathlib
import Definitions.Def_ChapterStrichartzWave
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left
open BookProof.StrichartzWave











open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (f : 𝓢(V, ℂ)) (u : Lp ℂ 2 (volume : Measure V)) :
    (inner ℂ (f.toLp 2 (volume : Measure V)) u : ℂ)
      = ∫ x, (starRingEnd ℂ) ((𝓕 f : 𝓢(V, ℂ)) x) * ((𝓕 u : Lp ℂ 2 (volume : Measure V)) x) := by

  rw [← MeasureTheory.Lp.inner_fourier_eq (f.toLp 2 (volume : Measure V)) u,
    SchwartzMap.toLp_fourier_eq, inner_toLp_left]
