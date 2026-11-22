-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.card_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:10.127901+00:00
-- url     : https://prove2.me/submissions/c03bae19-8dba-4a5a-8a57-8fbe7cb53ccd

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_neg_one_ne_one
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_card_units

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
theorem _root_.solution (n : ℕ) : Nat.card ((ZMod (2 ^ (n + 2)))ˣ ⧸
    Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) = 2 ^ n := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ))
  rw [Nat.card_zpowers, orderOf_eq_prime (neg_one_sq) (neg_one_ne_one n)] at h1
  have h2 : Nat.card (ZMod (2 ^ (n + 2)))ˣ = 2 ^ n * 2 := by
    have := card_units (n + 1)
    rw [pow_succ] at this
    exact this
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_right two_pos h1).symm
end Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
