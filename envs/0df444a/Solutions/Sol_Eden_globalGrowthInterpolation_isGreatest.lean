-- Prove2me | solution 1 for Eden.globalGrowthInterpolation_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:17:09.195+00:00
-- url     : https://prove2.me/submissions/328e589e-537f-4532-b04a-be8de682d905

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_GlobalGrowthDimension
import Theorems.Thm_Eden_globalGrowthInterpolation_four_five
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDefect_at_one
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_spectralProduct_zero
import Theorems.Thm_Eden_spectrumInterpolation_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_targetDimension_bounds
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDefect_at_one
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.spectrumInterpolation_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ globalGrowthInterpolation c d}
      (targetDimension c) := by
  have hd := targetDimension_bounds hc
  have hpos : 0 < c := by linarith
  have hroot : globalGrowthInterpolation c (targetDimension c) = 0 := by
    rw [globalGrowthInterpolation_four_five hc.le hd.1.le hd.2.le]
    simp only [targetDimension, add_sub_cancel_left]
    rw [mul_div_cancel₀ _ hpos.ne', sub_self]
  constructor
  · exact ⟨⟨by linarith, hd.2.le⟩, hroot ▸ le_rfl⟩
  · intro d hd'
    change d ∈ Icc 0 5 ∧ 0 ≤ globalGrowthInterpolation c d at hd'
    by_contra hn
    have hdt : targetDimension c < d := lt_of_not_ge hn
    have hd₄ : 4 ≤ d := hd.1.le.trans hdt.le
    rw [globalGrowthInterpolation_four_five hc.le hd₄ hd'.1.2] at hd'
    have hineq : 4 / c < d - 4 := by
      dsimp [targetDimension] at hdt
      linarith
    have hmul : 4 < (d - 4) * c := (div_lt_iff₀ hpos).mp hineq
    nlinarith [hd'.2]
end Eden
