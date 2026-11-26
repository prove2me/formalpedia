-- Prove2me | solution 1 for Eden.hasDerivAt_evolution_of_mem_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:14.541738+00:00
-- url     : https://prove2.me/submissions/265e2c3e-457d-4212-aac7-063c6683779a

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_CompleteTrajectories
import Theorems.Thm_Eden_amplitudeSq_pos_on_interval
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_hasDerivAt_euclidean_of_coord
import Theorems.Thm_Eden_hasDerivAt_planarX_of_pos
import Theorems.Thm_Eden_hasDerivAt_planarY_of_pos
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_pos_on_interval
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
attribute [local simp] Eden.evolution_zero_time
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
open Eden
namespace Eden
theorem _root_.solution (c t : ℝ) {p : PhaseSpace}
    (hp : p ∈ attractor) :
    HasDerivAt (fun τ => evolution c τ p) (vectorField c (evolution c t p)) t := by
  have hs₁ : 0 ≤ p 0 ^ 2 + p 1 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs₂ : 0 ≤ p 2 ^ 2 + p 3 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hD₁ := radialDiscriminant_pos_on_interval t hs₁ hp.1
  have hD₂ := radialDiscriminant_pos_on_interval t hs₂ hp.2.1
  have hB₁ := amplitudeSq_pos_on_interval t hs₁ hp.1
  have hB₂ := amplitudeSq_pos_on_interval t hs₂ hp.2.1
  apply hasDerivAt_euclidean_of_coord
  intro i
  fin_cases i
  · simpa [evolution, vectorField, radiusSq₁] using hasDerivAt_planarX_of_pos 1 hD₁ hB₁
  · simpa [evolution, vectorField, radiusSq₁] using hasDerivAt_planarY_of_pos 1 hD₁ hB₁
  · simpa [evolution, vectorField, radiusSq₂] using hasDerivAt_planarX_of_pos (Real.sqrt 2) hD₂ hB₂
  · simpa [evolution, vectorField, radiusSq₂] using hasDerivAt_planarY_of_pos (Real.sqrt 2) hD₂ hB₂
  · have hw := (((hasDerivAt_id t).const_mul (-c)).exp).mul_const (p 4)
    simpa [evolution, vectorField, mul_assoc, mul_comm, mul_left_comm] using hw
end Eden
