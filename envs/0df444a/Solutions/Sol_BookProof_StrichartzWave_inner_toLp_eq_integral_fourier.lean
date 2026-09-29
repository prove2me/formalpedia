-- Prove2me | solution 1 for BookProof.StrichartzWave.inner_toLp_eq_integral_fourier
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:36:54.20773+00:00
-- url     : https://prove2.me/submissions/1ebdf729-2fc7-42ba-8c9d-89518487a4a4

-- Generated from ChapterStrichartzWave.lean — solution of BookProof.StrichartzWave.inner_toLp_eq_integral_fourier
import Mathlib
import Definitions.Def_ChapterStrichartzWave
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left
open BookProof.StrichartzWave











open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (f g : 𝓢(V, ℂ)) :
    (inner ℂ (f.toLp 2 (volume : Measure V)) (g.toLp 2 (volume : Measure V)) : ℂ)
      = ∫ x, (starRingEnd ℂ) ((𝓕 f : 𝓢(V, ℂ)) x) * ((𝓕 g : 𝓢(V, ℂ)) x) := by

  rw [← MeasureTheory.Lp.inner_fourier_eq (f.toLp 2 (volume : Measure V))
      (g.toLp 2 (volume : Measure V)), SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq,
    inner_toLp_left]
  refine integral_congr_ae ?_
  filter_upwards [(𝓕 g : 𝓢(V, ℂ)).coeFn_toLp 2 (volume : Measure V)] with x hx
  rw [hx]
