-- Prove2me | solution 1 for Eden.hasDerivAt_frequencyEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:24:32.398317+00:00
-- url     : https://prove2.me/submissions/3ffe1c58-6960-4e36-8544-debad8ebadd3

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_FrequencyEvolution
import Theorems.Thm_Eden_frequencyEvolution_zero_time
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_hasDerivAt_euclidean_of_coord
import Theorems.Thm_Eden_hasDerivAt_planarX
import Theorems.Thm_Eden_hasDerivAt_planarY
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
theorem _root_.solution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    HasDerivAt (fun τ => frequencyEvolution c ν τ p)
      (frequencyVectorField c ν (frequencyEvolution c ν t p)) t := by
  apply hasDerivAt_euclidean_of_coord
  intro i
  fin_cases i
  · simpa [frequencyEvolution, frequencyVectorField, radiusSq₁] using
      hasDerivAt_planarX 1 ht (p 0) (p 1)
  · simpa [frequencyEvolution, frequencyVectorField, radiusSq₁] using
      hasDerivAt_planarY 1 ht (p 0) (p 1)
  · simpa [frequencyEvolution, frequencyVectorField, radiusSq₂] using
      hasDerivAt_planarX ν ht (p 2) (p 3)
  · simpa [frequencyEvolution, frequencyVectorField, radiusSq₂] using
      hasDerivAt_planarY ν ht (p 2) (p 3)
  · have hw := (((hasDerivAt_id t).const_mul (-c)).exp).mul_const (p 4)
    simpa [frequencyEvolution, frequencyVectorField, mul_assoc, mul_comm, mul_left_comm] using hw
end Eden
