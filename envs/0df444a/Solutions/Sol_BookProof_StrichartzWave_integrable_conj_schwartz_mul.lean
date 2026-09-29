-- Prove2me | solution 1 for BookProof.StrichartzWave.integrable_conj_schwartz_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T13:24:36.023897+00:00
-- url     : https://prove2.me/submissions/480f966c-b086-4670-9be4-c508230fb969

-- Generated from ChapterStrichartzWave.lean — solution of BookProof.StrichartzWave.integrable_conj_schwartz_mul
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave











open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (f : 𝓢(V, ℂ)) (u : Lp ℂ 2 (volume : Measure V)) :
    Integrable (fun x => (starRingEnd ℂ) (f x) * (u x)) (volume : Measure V) := by

  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (f.toLp 2 (volume : Measure V)) u
  refine h.congr ?_
  filter_upwards [f.coeFn_toLp 2 (volume : Measure V)] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]
