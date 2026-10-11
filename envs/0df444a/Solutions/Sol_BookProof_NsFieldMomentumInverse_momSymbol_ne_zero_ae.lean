-- Prove2me | solution 1 for BookProof.NsFieldMomentumInverse.momSymbol_ne_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:43:48.634987+00:00
-- url     : https://prove2.me/submissions/a7c5ba00-5415-4a01-881f-8d1406dfa330

-- Generated from ChapterNsFieldMomentumInverse.lean — solution of BookProof.NsFieldMomentumInverse.momSymbol_ne_zero_ae
import Mathlib
import Definitions.Def_ChapterNsFieldMomentumInverse
import Theorems.Thm_BookProof_NsFieldMomentumInverse_volume_momSymbol_zero
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
open BookProof.NsFieldMomentumInverse




open MeasureTheory SchwartzMap FourierTransform
open BookProof.NsSpatialMultiplier BookProof.FourierMultiplierEsa BookProof.StrichartzWave

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

set_option maxHeartbeats 1000000 in
theorem solution {m : W} (hm : m ≠ 0) :
    ∀ᵐ ξ ∂(volume : Measure W), momSymbol m ξ ≠ 0 := by

  have h := volume_momSymbol_zero hm
  rw [MeasureTheory.ae_iff]
  simpa using h
