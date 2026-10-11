-- Prove2me | solution 1 for BookProof.NsFieldMomentumInverse.eq_div_of_mul_eq_ae
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:55:14.093557+00:00
-- url     : https://prove2.me/submissions/05d3580b-12df-4af4-b4eb-4f198e4d6a4d

-- Generated from ChapterNsFieldMomentumInverse.lean — solution of BookProof.NsFieldMomentumInverse.eq_div_of_mul_eq_ae
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
theorem solution {m : W} (hm : m ≠ 0) (t : W → ℂ) (p : ℂ)
    (h : ∀ᵐ ξ ∂(volume : Measure W), ((momSymbol m ξ : ℝ) : ℂ) * t ξ = p) :
    ∀ᵐ ξ ∂(volume : Measure W), t ξ = p / ((momSymbol m ξ : ℝ) : ℂ) := by

  filter_upwards [h, momSymbol_ne_zero_ae hm] with ξ hξ hσ
  have hσ' : ((momSymbol m ξ : ℝ) : ℂ) ≠ 0 := by simpa using hσ
  rw [eq_div_iff hσ', mul_comm]
  exact hξ
