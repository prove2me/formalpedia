-- Prove2me | solution 1 for Eden.frequencyCorrection_image_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:00.274424+00:00
-- url     : https://prove2.me/submissions/64e812d0-ac93-442e-882e-80d8cdf8a5e0

import Definitions.Def_Eden_FrequencyEvolution
import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_FrequencyRotation
import Theorems.Thm_Eden_frequencyCorrection_mem_torus_iff
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_frequencyEvolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.frequencyEvolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (ν t : ℝ) :
    frequencyCorrection ν t '' torus = torus := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (frequencyCorrection_mem_torus_iff ν t q).2 hq
  · intro hp
    refine ⟨(frequencyCorrection ν t).symm p, ?_, (frequencyCorrection ν t).apply_symm_apply p⟩
    apply (frequencyCorrection_mem_torus_iff ν t _).1
    simpa using hp
end Eden
