-- Prove2me | solution 1 for Eden.frequency_attractor_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:17:57.285714+00:00
-- url     : https://prove2.me/submissions/f260b75b-45ad-4900-ae65-4e1cf0424283

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_TorusAngles
import Definitions.Def_Eden_FrequencyAttractor
import Theorems.Thm_Eden_frequencyEvolution_image_attractor
import Theorems.Thm_Eden_frequencyUniformlyAttractsBounded_nonempty
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_frequencyEvolution_zero_time
import Theorems.Thm_Eden_isCompact_attractor
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_radiusEvolution_at_one
import Theorems.Thm_Eden_radiusEvolution_at_sqrt_two
import Theorems.Thm_Eden_radiusEvolution_at_zero
import Theorems.Thm_Eden_radiusEvolution_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_origin
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
attribute [local simp] Eden.radiusEvolution_at_one
attribute [local simp] Eden.radiusEvolution_at_sqrt_two
attribute [local simp] Eden.radiusEvolution_at_zero
attribute [local simp] Eden.radiusEvolution_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c ν : ℝ} {C : Set PhaseSpace}
    (hclosed : IsClosed C) (hC : FrequencyUniformlyAttractsBounded c ν C) : attractor ⊆ C := by
  intro p hp
  apply (hclosed.mem_iff_infDist_zero (frequencyUniformlyAttractsBounded_nonempty hC)).2
  apply le_antisymm _ Metric.infDist_nonneg
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨T, hT₀, hT⟩ := hC attractor isCompact_attractor.isBounded ε hε
  have himage := frequencyEvolution_image_attractor c ν hT₀
  obtain ⟨q, hq, hqp⟩ := (show p ∈ frequencyEvolution c ν T '' attractor by rw [himage]; exact hp)
  obtain ⟨r, hr, hpr⟩ := hT T le_rfl q hq
  rw [hqp] at hpr
  simpa only [zero_add] using (Metric.infDist_le_dist_of_mem hr).trans_lt hpr
end Eden
