-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.neg_not_mem_five
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:30.57641+00:00
-- url     : https://prove2.me/submissions/cd3cf3be-5788-4378-a1b5-9e3ca55d8ef0

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_mod_four_reduction_five
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_mod_four_reduction_neg_one
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_mem_zpowers_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
namespace Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
theorem _root_.solution (n : ℕ) :
    (-1 : (ZMod (2 ^ (n + 2)))ˣ) ∉ Subgroup.zpowers (u5 (n + 2)) := by
  intro hm
  obtain ⟨k, hk⟩ := mem_zpowers_nat hm
  have h4 : 4 ∣ 2 ^ (n + 2) := ⟨2 ^ n, by ring⟩
  have := congrArg (r4 (n + 2) h4) hk
  rw [map_pow, mod_four_reduction_five, mod_four_reduction_neg_one, one_pow] at this
  exact absurd this (by decide)
end Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
