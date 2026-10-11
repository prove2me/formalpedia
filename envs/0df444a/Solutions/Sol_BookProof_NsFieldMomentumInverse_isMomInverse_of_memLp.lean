-- Prove2me | solution 1 for BookProof.NsFieldMomentumInverse.isMomInverse_of_memLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:44:19.345755+00:00
-- url     : https://prove2.me/submissions/c68b3d33-58fc-4ec3-a513-ec715c445965

-- Generated from ChapterNsFieldMomentumInverse.lean — solution of BookProof.NsFieldMomentumInverse.isMomInverse_of_memLp
import Mathlib
import Definitions.Def_ChapterNsFieldMomentumInverse
import Theorems.Thm_BookProof_NsFieldMomentumInverse_momSymbol_ne_zero_ae
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
theorem solution {m : W} (hm : m ≠ 0) (f : Lp ℂ 2 (volume : Measure W))
    (hf : MemLp (fun ξ => (f : W → ℂ) ξ / ((momSymbol m ξ : ℝ) : ℂ)) 2 (volume : Measure W)) :
    IsMomInverse m f hf.toLp := by

  filter_upwards [hf.coeFn_toLp, momSymbol_ne_zero_ae hm] with ξ hξ hσ
  rw [hξ]
  have : ((momSymbol m ξ : ℝ) : ℂ) ≠ 0 := by simpa using hσ
  field_simp
