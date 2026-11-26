-- Prove2me | solution 1 for Eden.spectrumInterpolation_pos_one_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:09:55.582886+00:00
-- url     : https://prove2.me/submissions/b7c63c52-0aeb-4ded-97e8-775f350cf1bc

import Definitions.Def_Eden_InterpolationSign
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_LimitingInterpolation
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_exists_dimension_segment
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
import Theorems.Thm_Eden_spectrumInterpolation_interpolate
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
theorem _root_.solution {c d : ℝ} (hc : 4 < c)
    (hd : d ∈ Ioo 0 (targetDimension c)) :
    0 < spectrumInterpolation ![2, 2, 0, 0, -c] d := by
  obtain ⟨k, hk, α, hα, rfl⟩ := exists_dimension_segment
    (show d ∈ Icc 0 5 from ⟨hd.1.le, hd.2.le.trans (targetDimension_bounds hc).2.le⟩)
  rw [spectrumInterpolation_interpolate _ hk hα.1 hα.2]
  interval_cases k <;>
    norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ] at *
  · linarith [hd.1]
  · linarith [hα.1]
  · have hαc : α * c < 4 := (lt_div_iff₀ (show 0 < c by linarith)).mp
      (show α < 4 / c by dsimp [targetDimension] at hd; linarith [hd.2])
    nlinarith
end Eden
