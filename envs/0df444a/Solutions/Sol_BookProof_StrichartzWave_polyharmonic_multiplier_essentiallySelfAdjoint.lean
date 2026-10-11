-- Prove2me | solution 1 for BookProof.StrichartzWave.polyharmonic_multiplier_essentiallySelfAdjoint
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:28:10.265986+00:00
-- url     : https://prove2.me/submissions/5d9ded13-c517-48fd-8b53-e109155c139b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterWaveUnboundedPotential.lean — solution of BookProof.StrichartzWave.polyharmonic_multiplier_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Theorems.Thm_BookProof_StrichartzWave_multiplierOp_essentiallySelfAdjoint
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V)
      (opL2 (multiplierOp (fun ξ : V => (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ k))) := by

  have h : Function.HasTemperateGrowth (fun ξ : V => (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ k) :=
    (((Function.HasTemperateGrowth.const (4 * Real.pi ^ 2)).mul
      (Function.hasTemperateGrowth_norm_sq (H := V))).pow k)
  exact multiplierOp_essentiallySelfAdjoint _ h
