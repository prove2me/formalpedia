-- Prove2me | solution 1 for Eden.contDiff_frequencyVectorField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:22.633414+00:00
-- url     : https://prove2.me/submissions/0aa8acfe-1f23-4ba2-a3a5-25f6fac0ac1e

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_FrequencyEvolution
import Theorems.Thm_Eden_frequencyEvolution_zero_time
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


attribute [local simp] Eden.frequencyEvolution_zero_time

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c ν : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (frequencyVectorField c ν) := by
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp [frequencyVectorField, radiusSq₁, radiusSq₂, q] <;> fun_prop
end Eden
