-- Prove2me | solution 1 for BookProof.StrichartzWave.schwartzEquiv_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T13:24:58.499581+00:00
-- url     : https://prove2.me/submissions/e91919f7-40d8-4fa8-8ecf-73cbe8e82329

-- Generated from ChapterStrichartzWave.lean — solution of BookProof.StrichartzWave.schwartzEquiv_coe
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave











open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (f : 𝓢(V, ℂ)) :
    ((schwartzEquiv V f : schwartzDomain V) : Lp ℂ 2 (volume : Measure V))
      = f.toLp 2 (volume : Measure V) := rfl
