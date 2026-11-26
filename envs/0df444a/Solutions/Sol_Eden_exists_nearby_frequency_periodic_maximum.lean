-- Prove2me | solution 1 for Eden.exists_nearby_frequency_periodic_maximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:01.436933+00:00
-- url     : https://prove2.me/submissions/6a71a34a-4cc3-4402-aed2-0961090e5e6e

import Definitions.Def_Eden_FrequencyDimensions
import Definitions.Def_Eden_FrequencyAttractor
import Definitions.Def_Eden_FrequencyUniqueness
import Mathlib.Topology.Instances.Rat
import Definitions.Def_Eden_RationalFrequency
import Theorems.Thm_Eden_frequency_periodic_asymptotic_isGreatest
import Theorems.Thm_Eden_frequency_periodic_finiteTime_isGreatest
import Theorems.Thm_Eden_exists_positive_rational_frequency

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c ε : ℝ} (hc : 4 < c) (hε : 0 < ε) :
    ∃ ν : ℚ, 0 < ν ∧ |(ν : ℝ) - Real.sqrt 2| < ε ∧
      IsGreatest (frequencyAsymptoticDimension c ν '' frequencyPeriodicSet c ν)
        (targetDimension c) ∧
      ∀ t : ℝ, 0 < t →
        IsGreatest (frequencyFiniteTimeDimension c ν t '' frequencyPeriodicSet c ν)
          (targetDimension c) := by
  obtain ⟨ν, hν, hclose⟩ := exists_positive_rational_frequency hε
  exact ⟨ν, hν, hclose, frequency_periodic_asymptotic_isGreatest hc ν,
    fun _ ht => frequency_periodic_finiteTime_isGreatest hc ν ht⟩
end Eden
