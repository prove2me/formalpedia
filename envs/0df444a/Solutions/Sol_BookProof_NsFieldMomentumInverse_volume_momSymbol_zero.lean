-- Prove2me | solution 1 for BookProof.NsFieldMomentumInverse.volume_momSymbol_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:43:33.739079+00:00
-- url     : https://prove2.me/submissions/0765b2ca-e7b8-4b3b-8989-dac73f038e9b

-- Generated from ChapterNsFieldMomentumInverse.lean — solution of BookProof.NsFieldMomentumInverse.volume_momSymbol_zero
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
theorem solution {m : W} (hm : m ≠ 0) :
    (volume : Measure W) {ξ : W | momSymbol m ξ = 0} = 0 := by

  have h : {ξ : W | momSymbol m ξ = 0}
      = (LinearMap.ker ((innerSL ℝ m : W →L[ℝ] ℝ).toLinearMap) : Submodule ℝ W) := by
    ext x
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply, momSymbol]
    rw [real_inner_comm]
    constructor
    · intro hx
      have : (2 * Real.pi) ≠ 0 := by positivity
      exact (mul_eq_zero.mp hx).resolve_left this
    · intro hx
      rw [hx, mul_zero]
  rw [h]
  refine Measure.addHaar_submodule _ _ ?_
  intro htop
  have hmem : m ∈ LinearMap.ker ((innerSL ℝ m : W →L[ℝ] ℝ).toLinearMap) := by
    rw [htop]; trivial
  have hm' : (inner ℝ m m : ℝ) = 0 := by simpa [LinearMap.mem_ker] using hmem
  exact hm (inner_self_eq_zero.mp hm')
