-- Prove2me | solution 1 for BookProof.StrichartzWave.constCoeffOp_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:39:14.472462+00:00
-- url     : https://prove2.me/submissions/7d35d5b7-a2ee-44ef-8494-a87964ed0f2a

-- Generated from ChapterStrichartzWave.lean — solution of BookProof.StrichartzWave.constCoeffOp_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterStrichartzWave
import Theorems.Thm_BookProof_StrichartzWave_constCoeffOp_deficiencyTrivial
open BookProof.StrichartzWave











open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (c : ι → ℝ) (w : ι → V) (κ : ℝ) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V)
      (opL2 (constCoeffOp c w κ)) :=
  ⟨constCoeffOp_deficiencyTrivial c w κ (by simp),
      constCoeffOp_deficiencyTrivial c w κ (by simp)⟩
