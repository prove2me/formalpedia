-- Prove2me | solution 1 for BookProof.StrichartzWave.multiplierOp_essentiallySelfAdjoint
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:27:53.367111+00:00
-- url     : https://prove2.me/submissions/6f65ce0e-b9e3-43a0-9145-60fc921af1a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterWaveUnboundedPotential.lean — solution of BookProof.StrichartzWave.multiplierOp_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Theorems.Thm_BookProof_StrichartzWave_multiplierOp_deficiencyTrivial
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (m : V → ℝ) (hm : Function.HasTemperateGrowth m) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (multiplierOp m)) :=
  ⟨multiplierOp_deficiencyTrivial m hm (by simp),
      multiplierOp_deficiencyTrivial m hm (by simp)⟩
