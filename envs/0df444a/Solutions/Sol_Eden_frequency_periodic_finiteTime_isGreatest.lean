-- Prove2me | solution 1 for Eden.frequency_periodic_finiteTime_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:04:05.416856+00:00
-- url     : https://prove2.me/submissions/14d4a54a-910a-4296-9464-90174368277b

import Definitions.Def_Eden_FrequencyDimensions
import Definitions.Def_Eden_FrequencyAttractor
import Definitions.Def_Eden_FrequencyUniqueness
import Mathlib.Topology.Instances.Rat
import Definitions.Def_Eden_RationalFrequency
import Theorems.Thm_Eden_torus_subset_frequencyPeriodicSet
import Theorems.Thm_Eden_frequencyFiniteTimeDimension_bound_and_eq
import Theorems.Thm_Eden_torus_nonempty
import Theorems.Thm_Eden_torus_subset_attractor


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c)
    (ν : ℚ) (ht : 0 < t) :
    IsGreatest (frequencyFiniteTimeDimension c ν t '' frequencyPeriodicSet c ν)
      (targetDimension c) := by
  constructor
  · obtain ⟨p, hp⟩ := torus_nonempty
    exact ⟨p, torus_subset_frequencyPeriodicSet c ν hp,
      (frequencyFiniteTimeDimension_bound_and_eq hc ν ht (torus_subset_attractor hp)).2.mpr hp⟩
  · rintro d ⟨p, hp, rfl⟩
    exact (frequencyFiniteTimeDimension_bound_and_eq hc ν ht hp.1).1
end Eden
