-- Prove2me | solution 1 for Eden.torus_subset_frequencyPeriodicSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:05.861941+00:00
-- url     : https://prove2.me/submissions/bb03a3ab-6b7b-4eb7-992e-6b86b9286667

import Definitions.Def_Eden_FrequencyDimensions
import Definitions.Def_Eden_FrequencyAttractor
import Definitions.Def_Eden_FrequencyUniqueness
import Mathlib.Topology.Instances.Rat
import Definitions.Def_Eden_RationalFrequency
import Theorems.Thm_Eden_frequency_torus_common_return
import Theorems.Thm_Eden_rational_frequency_torus_period
import Theorems.Thm_Eden_frequency_torus_not_equilibrium
import Theorems.Thm_Eden_torus_subset_attractor


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (ν : ℚ) :
    torus ⊆ frequencyPeriodicSet c (ν : ℝ) := by
  intro p hp
  refine ⟨torus_subset_attractor hp, frequency_torus_not_equilibrium c ν hp,
    2 * Real.pi * ν.den, (rational_frequency_torus_period c ν hp).1, ?_⟩
  exact frequency_torus_common_return c ν.pos (Rat.cast_def ν) hp
end Eden
