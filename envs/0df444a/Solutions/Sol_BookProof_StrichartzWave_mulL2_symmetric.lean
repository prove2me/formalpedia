-- Prove2me | solution 1 for BookProof.StrichartzWave.mulL2_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:25:57.225684+00:00
-- url     : https://prove2.me/submissions/f289c5bb-853b-4d04-afc4-7eda097ea5e8

-- Generated from ChapterWaveBoundedPotential.lean — solution of BookProof.StrichartzWave.mulL2_symmetric
import Mathlib
import Definitions.Def_ChapterWaveBoundedPotential
import Theorems.Thm_BookProof_StrichartzWave_mulL2_coeFn
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (W : Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V))
    (hW : ∀ᵐ x ∂(volume : Measure V), (starRingEnd ℂ) (W x) = W x)
    (u w : Lp ℂ 2 (volume : Measure V)) :
    (inner ℂ (mulL2 W u) w : ℂ) = inner ℂ u (mulL2 W w) := by

  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulL2_coeFn W u, mulL2_coeFn W w, hW] with x hx hy hreal
  rw [hx, hy]
  simp only [RCLike.inner_apply, map_mul, hreal]
  ring
