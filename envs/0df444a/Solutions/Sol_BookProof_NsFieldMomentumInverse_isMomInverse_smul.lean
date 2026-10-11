-- Prove2me | solution 1 for BookProof.NsFieldMomentumInverse.isMomInverse_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:55:12.904331+00:00
-- url     : https://prove2.me/submissions/df44b464-70a3-45c2-b9bb-7de36f7a3b15

-- Generated from ChapterNsFieldMomentumInverse.lean — solution of BookProof.NsFieldMomentumInverse.isMomInverse_smul
import Mathlib
import Definitions.Def_ChapterNsFieldMomentumInverse
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
theorem solution {m : W} (c : ℂ) {f g : Lp ℂ 2 (volume : Measure W)}
    (h : IsMomInverse m f g) : IsMomInverse m (c • f) (c • g) := by

  filter_upwards [h, MeasureTheory.Lp.coeFn_smul c g, MeasureTheory.Lp.coeFn_smul c f]
    with ξ hx hg hf
  rw [hg, hf]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, mul_comm _ c, mul_assoc, hx]
