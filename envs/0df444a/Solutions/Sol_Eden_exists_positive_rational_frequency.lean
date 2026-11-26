-- Prove2me | solution 1 for Eden.exists_positive_rational_frequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:56:58.623553+00:00
-- url     : https://prove2.me/submissions/62202375-9ee7-4e7f-869f-7ded6929e179

import Definitions.Def_Eden_FrequencyDimensions
import Definitions.Def_Eden_FrequencyAttractor
import Definitions.Def_Eden_FrequencyUniqueness
import Mathlib.Topology.Instances.Rat
import Definitions.Def_Eden_RationalFrequency

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) :
    ∃ ν : ℚ, 0 < ν ∧ |(ν : ℝ) - Real.sqrt 2| < ε := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨ν, hν₀, hν₁⟩ := exists_rat_btwn
    (show max 0 (Real.sqrt 2 - ε) < Real.sqrt 2 + ε by
      exact max_lt (by linarith) (by linarith))
  refine ⟨ν, ?_, ?_⟩
  · exact_mod_cast (lt_of_le_of_lt (le_max_left 0 _) hν₀)
  · rw [abs_lt]
    constructor <;> linarith [le_max_right 0 (Real.sqrt 2 - ε)]
end Eden
