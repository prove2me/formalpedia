-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.neg_not_mem_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:49:04.382293+00:00
-- url     : https://prove2.me/submissions/eea316e2-0a05-41d5-8f66-853f802cb543

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_mod_eight_reduction_three
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_mod_eight_reduction_neg_one
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
    (-1 : (ZMod (2 ^ (n + 3)))ˣ) ∉ Subgroup.zpowers (u3 (n + 3)) := by
  intro hm
  obtain ⟨k, hk⟩ := mem_zpowers_nat hm
  have h8 : 8 ∣ 2 ^ (n + 3) := ⟨2 ^ n, by ring⟩
  have := congrArg (r8 (n + 3) h8) hk
  rw [map_pow, mod_eight_reduction_three, mod_eight_reduction_neg_one] at this
  have h9 : (3 : ZMod 8) ^ 2 = 1 := by decide
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [pow_mul, h9, one_pow] at this
    exact absurd this (by decide)
  · rw [pow_succ, pow_mul, h9, one_pow, one_mul] at this
    exact absurd this (by decide)
end Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
