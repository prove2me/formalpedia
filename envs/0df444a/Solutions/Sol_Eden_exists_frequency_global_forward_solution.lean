-- Prove2me | solution 1 for Eden.exists_frequency_global_forward_solution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:46.830731+00:00
-- url     : https://prove2.me/submissions/948872a7-69d7-44a4-b69d-f617086a9683

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_FrequencyEvolution
import Theorems.Thm_Eden_frequencyEvolution_zero_time
import Theorems.Thm_Eden_hasDerivAt_frequencyEvolution
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
theorem _root_.solution (c ν : ℝ) (p : PhaseSpace) :
    ∃ f : ℝ → PhaseSpace, f 0 = p ∧
      ∀ t, 0 ≤ t → HasDerivAt f (frequencyVectorField c ν (f t)) t :=
  ⟨fun t => frequencyEvolution c ν t p, frequencyEvolution_zero_time c ν p,
    fun _ ht => hasDerivAt_frequencyEvolution c ν ht p⟩
end Eden
