-- Prove2me | solution 1 for Eden.dist_attractorProjection_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:57.738696+00:00
-- url     : https://prove2.me/submissions/51904ec0-a6fd-4047-bbb5-b2c2704decb6

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Eden_AttractorDistance
import Theorems.Thm_Eden_discScale_distance_sq
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_norm_sq_phaseSpace
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
theorem _root_.solution (p : PhaseSpace) :
    dist p (attractorProjection p) ^ 2 =
      max (Real.sqrt (radiusSq₁ p) - Real.sqrt 2) 0 ^ 2 +
      max (Real.sqrt (radiusSq₂ p) - Real.sqrt 2) 0 ^ 2 + p 4 ^ 2 := by
  rw [dist_eq_norm, norm_sq_phaseSpace]
  change ((p 0 - discScale (Real.sqrt (radiusSq₁ p)) * p 0) ^ 2 +
    (p 1 - discScale (Real.sqrt (radiusSq₁ p)) * p 1) ^ 2) +
    ((p 2 - discScale (Real.sqrt (radiusSq₂ p)) * p 2) ^ 2 +
    (p 3 - discScale (Real.sqrt (radiusSq₂ p)) * p 3) ^ 2) + (p 4 - 0) ^ 2 = _
  dsimp only [radiusSq₁, radiusSq₂]
  rw [discScale_distance_sq (p 0) (p 1), discScale_distance_sq (p 2) (p 3), sub_zero]
end Eden
