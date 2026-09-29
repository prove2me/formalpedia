-- Prove2me | solution 1 for BookProof.StrichartzWave.contDiff_symbolFn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:57:16.935295+00:00
-- url     : https://prove2.me/submissions/aba445c4-a318-4e77-abcd-0d9183489834

-- Generated from ChapterStrichartzWave.lean — solution of BookProof.StrichartzWave.contDiff_symbolFn
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave











open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem solution (c : ι → ℝ) (w : ι → V) (κ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (symbolFn c w κ) := by

  unfold symbolFn
  apply ContDiff.add _ contDiff_const
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul ((((innerSL ℝ).flip (w i)).contDiff).pow 2)
