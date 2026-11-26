-- Prove2me | solution 1 for Eden.radiusSq_frequencyEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:17:15.058299+00:00
-- url     : https://prove2.me/submissions/ddf892d0-2fec-41eb-9d5d-919840a6bae3

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_FrequencyEvolution
import Theorems.Thm_Eden_planar_radius_sq


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₁ (frequencyEvolution c ν t p) = squaredRadiusEvolution t (radiusSq₁ p) ∧
    radiusSq₂ (frequencyEvolution c ν t p) = squaredRadiusEvolution t (radiusSq₂ p) := by
  constructor
  · exact planar_radius_sq 1 ht _ _
  · exact planar_radius_sq ν ht _ _
end Eden
