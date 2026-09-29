-- Prove2me | solution 1 for BookProof.StrichartzWave.inner_toLp_left
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T13:24:24.247547+00:00
-- url     : https://prove2.me/submissions/07600c5a-abe9-4039-b848-53740e32422a

-- Generated from ChapterStrichartzWave.lean — solution of BookProof.StrichartzWave.inner_toLp_left
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave











open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (f : 𝓢(V, ℂ)) (u : Lp ℂ 2 (volume : Measure V)) :
    (inner ℂ (f.toLp 2 (volume : Measure V)) u : ℂ)
      = ∫ x, (starRingEnd ℂ) (f x) * (u x) := by

  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [f.coeFn_toLp 2 (volume : Measure V)] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]
