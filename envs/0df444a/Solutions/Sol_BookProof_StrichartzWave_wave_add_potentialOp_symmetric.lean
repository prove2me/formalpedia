-- Prove2me | solution 1 for BookProof.StrichartzWave.wave_add_potentialOp_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:26:03.957977+00:00
-- url     : https://prove2.me/submissions/c6f5f6e4-2af8-4259-ae6c-553799f7972b

-- Generated from ChapterWaveUnboundedPotential.lean — solution of BookProof.StrichartzWave.wave_add_potentialOp_symmetric
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Theorems.Thm_BookProof_StrichartzWave_potentialOp_symmetric
import Theorems.Thm_BookProof_StrichartzWave_opL2_add
import Theorems.Thm_BookProof_StrichartzWave_wave_symmetric
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : Function.HasTemperateGrowth W) :
    BookProof.FarisLavine.SymmetricOn (schwartzDomain (SpaceTime n))
      (opL2 (waveOp n 0 + potentialOp W)) := by

  intro x y
  have h1 := wave_symmetric n 0 x y
  have h2 := potentialOp_symmetric W hW x y
  simp only [opL2_add, LinearMap.add_apply, inner_add_left, inner_add_right]
  linear_combination h1 + h2
