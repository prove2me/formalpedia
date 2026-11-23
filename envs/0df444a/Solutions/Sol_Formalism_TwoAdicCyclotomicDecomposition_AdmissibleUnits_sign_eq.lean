-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.sign_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:54:48.017585+00:00
-- url     : https://prove2.me/submissions/cfdcb9ed-c2ea-4666-8428-43e904d33c69

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_mod_four_reduction_five
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_mod_four_reduction_neg_one

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
theorem _root_.solution (n : ℕ) {b b' : Bool} {k k' : ℕ}
    (h : (if b then -1 else 1) * u5 (n + 3) ^ k = (if b' then -1 else 1) * u5 (n + 3) ^ k') :
    b = b' := by
  have h4 : 4 ∣ 2 ^ (n + 3) := ⟨2 ^ (n + 1), by ring⟩
  have hr : ∀ c : Bool, r4 (n + 3) h4 (if c then -1 else 1) = if c then -1 else 1 := by
    intro c
    cases c
    · exact map_one _
    · exact mod_four_reduction_neg_one _ _
  have := congrArg (r4 (n + 3) h4) h
  rw [map_mul, map_mul, hr, hr, map_pow, map_pow, mod_four_reduction_five, one_pow, one_pow, mul_one, mul_one] at this
  cases b <;> cases b'
  · rfl
  · exact absurd this (by decide)
  · exact absurd this (by decide)
  · rfl
end Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
