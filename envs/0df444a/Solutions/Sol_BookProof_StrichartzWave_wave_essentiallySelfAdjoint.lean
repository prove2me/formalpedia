-- Prove2me | solution 1 for BookProof.StrichartzWave.wave_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:39:37.550287+00:00
-- url     : https://prove2.me/submissions/faa7f97d-8cc0-4728-b6e1-708650ddec00

-- Generated from ChapterStrichartzWave.lean — solution of BookProof.StrichartzWave.wave_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterStrichartzWave
import Theorems.Thm_BookProof_StrichartzWave_constCoeffOp_essentiallySelfAdjoint
open BookProof.StrichartzWave











open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (κ : ℝ) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n))
      (opL2 (waveOp n κ)) := constCoeffOp_essentiallySelfAdjoint _ _ _
