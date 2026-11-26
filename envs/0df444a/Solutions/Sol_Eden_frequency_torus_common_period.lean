-- Prove2me | solution 1 for Eden.frequency_torus_common_period
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:58.164797+00:00
-- url     : https://prove2.me/submissions/29ae1198-5bfd-462c-be45-17b09ced6d84

import Definitions.Def_Eden_FrequencyDimensions
import Definitions.Def_Eden_FrequencyAttractor
import Definitions.Def_Eden_FrequencyUniqueness
import Mathlib.Topology.Instances.Rat
import Definitions.Def_Eden_RationalFrequency
import Theorems.Thm_Eden_frequencyEvolution_add_on_torus
import Theorems.Thm_Eden_frequency_torus_common_return

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {ν : ℝ} {a : ℤ} {b : ℕ}
    (hb : 0 < b) (hν : ν = (a : ℝ) / (b : ℝ)) {p : PhaseSpace} (hp : p ∈ torus) :
    0 < 2 * Real.pi * b ∧
      Function.Periodic (fun t : ℝ => frequencyEvolution c ν t p) (2 * Real.pi * b) := by
  constructor
  · positivity
  · intro t
    change frequencyEvolution c ν (t + 2 * Real.pi * b) p = frequencyEvolution c ν t p
    rw [add_comm t, frequencyEvolution_add_on_torus c ν _ t hp,
      frequency_torus_common_return c hb hν hp]
end Eden
