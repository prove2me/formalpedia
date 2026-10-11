-- Prove2me | solution 1 for BookProof.StrichartzWave.wave_add_potential_essentiallySelfAdjoint
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:25:58.956526+00:00
-- url     : https://prove2.me/submissions/36c7bb1b-b68a-4d1e-bc46-5a3bd7c1b263
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterWaveBoundedPotential.lean — solution of BookProof.StrichartzWave.wave_add_potential_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterWaveBoundedPotential
import Theorems.Thm_BookProof_StrichartzWave_wave_add_boundedPotential_essentiallySelfAdjoint
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
    (hW : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure (SpaceTime n))) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n))
      (opL2 (waveOp n 0) +
        ((mulL2 (hW.toLp _)).toLinearMap ∘ₗ (schwartzDomain (SpaceTime n)).subtype)) := by

  refine wave_add_boundedPotential_essentiallySelfAdjoint n (hW.toLp _) ?_
  filter_upwards [hW.coeFn_toLp] with x hx
  rw [hx]
  simp
