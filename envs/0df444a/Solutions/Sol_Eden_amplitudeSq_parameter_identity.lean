-- Prove2me | solution 1 for Eden.amplitudeSq_parameter_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:56.186244+00:00
-- url     : https://prove2.me/submissions/baacf89c-ceaa-41ca-a927-b4add4fd1712

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InitialDerivative
import Theorems.Thm_Eden_contDiff_amplitudeSq
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_hasDerivAt_squaredRadiusEvolution_parameter
import Theorems.Thm_Eden_mul_amplitudeSq
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



set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    amplitudeSq t s + s * deriv (amplitudeSq t) s =
      Real.exp (-4 * t) / Real.sqrt (radialDiscriminant t s) ^ 3 := by
  have hB := ((contDiff_amplitudeSq ht 1).differentiable one_ne_zero s).hasDerivAt
  have hp := (hasDerivAt_id s).mul hB
  change HasDerivAt (fun r => r * amplitudeSq t r)
    (1 * amplitudeSq t s + s * deriv (amplitudeSq t) s) s at hp
  have hS : HasDerivAt (squaredRadiusEvolution t)
      (amplitudeSq t s + s * deriv (amplitudeSq t) s) s := by
    simpa only [mul_amplitudeSq ht, one_mul] using hp
  exact hS.unique (hasDerivAt_squaredRadiusEvolution_parameter ht s)
end Eden
