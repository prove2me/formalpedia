-- Prove2me | solution 1 for BookProof.NsFieldMomentumInverse.momentum_kernel_trivial
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:43:49.77686+00:00
-- url     : https://prove2.me/submissions/c254c842-a48a-462a-9bcd-363449456203

-- Generated from ChapterNsFieldMomentumInverse.lean — solution of BookProof.NsFieldMomentumInverse.momentum_kernel_trivial
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
theorem solution {m : W} (hm : m ≠ 0) (g : Lp ℂ 2 (volume : Measure W))
    (h : IsMomInverse m 0 g) : g = 0 := by

  refine (MeasureTheory.Lp.eq_zero_iff_ae_eq_zero).2 ?_
  filter_upwards [h, momSymbol_ne_zero_ae hm,
    MeasureTheory.Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure W))] with ξ hξ hσ hz
  rw [hz] at hξ
  have : ((momSymbol m ξ : ℝ) : ℂ) ≠ 0 := by
    simpa using hσ
  exact (mul_eq_zero.mp hξ).resolve_left this
