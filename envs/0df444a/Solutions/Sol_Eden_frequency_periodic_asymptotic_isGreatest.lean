-- Prove2me | solution 1 for Eden.frequency_periodic_asymptotic_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:04:22.40605+00:00
-- url     : https://prove2.me/submissions/40d71c6a-93bd-4921-8e23-8ce0598ad548

import Definitions.Def_Eden_FrequencyDimensions
import Definitions.Def_Eden_FrequencyAttractor
import Definitions.Def_Eden_FrequencyUniqueness
import Mathlib.Topology.Instances.Rat
import Definitions.Def_Eden_RationalFrequency
import Theorems.Thm_Eden_torus_subset_frequencyPeriodicSet
import Theorems.Thm_Eden_frequencyAsymptoticDimension_bound_and_eq
import Theorems.Thm_Eden_torus_nonempty
import Theorems.Thm_Eden_torus_subset_attractor


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) (ν : ℚ) :
    IsGreatest (frequencyAsymptoticDimension c ν '' frequencyPeriodicSet c ν)
      (targetDimension c) := by
  constructor
  · obtain ⟨p, hp⟩ := torus_nonempty
    exact ⟨p, torus_subset_frequencyPeriodicSet c ν hp,
      (frequencyAsymptoticDimension_bound_and_eq hc ν (torus_subset_attractor hp)).2.mpr hp⟩
  · rintro d ⟨p, hp, rfl⟩
    exact (frequencyAsymptoticDimension_bound_and_eq hc ν hp.1).1
end Eden
