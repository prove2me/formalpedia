-- Prove2me | solution 1 for BookProof.StrichartzWave.wave_add_boundedPotentialOp_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:28:11.248806+00:00
-- url     : https://prove2.me/submissions/8e78b5c7-7200-48f5-b52f-5b9b285dc811

-- Generated from ChapterWaveUnboundedPotential.lean — solution of BookProof.StrichartzWave.wave_add_boundedPotentialOp_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Theorems.Thm_BookProof_StrichartzWave_opL2_add
import Theorems.Thm_BookProof_StrichartzWave_opL2_potentialOp_eq_mulL2
import Theorems.Thm_BookProof_StrichartzWave_wave_add_potential_essentiallySelfAdjoint
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterWaveBoundedPotential
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : Function.HasTemperateGrowth W)
    (hmem : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure (SpaceTime n))) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n))
      (opL2 (waveOp n 0 + potentialOp W)) := by

  rw [opL2_add, opL2_potentialOp_eq_mulL2 W hW hmem]
  exact wave_add_potential_essentiallySelfAdjoint n W hmem
