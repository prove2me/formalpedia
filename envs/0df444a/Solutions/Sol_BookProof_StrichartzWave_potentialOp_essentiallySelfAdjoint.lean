-- Prove2me | solution 1 for BookProof.StrichartzWave.potentialOp_essentiallySelfAdjoint
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:26:00.942226+00:00
-- url     : https://prove2.me/submissions/a0bfe5d1-b9f6-449f-ae98-adcfd43e338e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterWaveUnboundedPotential.lean — solution of BookProof.StrichartzWave.potentialOp_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Theorems.Thm_BookProof_StrichartzWave_potentialOp_deficiencyTrivial
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (W : V → ℝ) (hW : Function.HasTemperateGrowth W) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (potentialOp W)) :=
  ⟨potentialOp_deficiencyTrivial W hW (by simp),
      potentialOp_deficiencyTrivial W hW (by simp)⟩
