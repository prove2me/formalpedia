-- Prove2me | solution 1 for Eden.rational_frequency_torus_period
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:32.16954+00:00
-- url     : https://prove2.me/submissions/feda231c-fdcc-4865-913a-a37af71af212

import Definitions.Def_Eden_FrequencyDimensions
import Definitions.Def_Eden_FrequencyAttractor
import Definitions.Def_Eden_FrequencyUniqueness
import Mathlib.Topology.Instances.Rat
import Definitions.Def_Eden_RationalFrequency
import Theorems.Thm_Eden_frequency_torus_common_period

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (ν : ℚ) {p : PhaseSpace} (hp : p ∈ torus) :
    0 < 2 * Real.pi * ν.den ∧
      Function.Periodic (fun t : ℝ => frequencyEvolution c (ν : ℝ) t p) (2 * Real.pi * ν.den) := by
  exact frequency_torus_common_period c ν.pos (Rat.cast_def ν) hp
end Eden
