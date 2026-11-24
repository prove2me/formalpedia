-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.quotCyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:02:47.538276+00:00
-- url     : https://prove2.me/submissions/6410868e-9dc7-4d7e-8881-bff1d2180e53

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_neg_not_mem_five
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_neg_not_mem_three
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_orderOf_five_units_two_pow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_orderOf_three_units_two_pow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_orderOf_mk_eq
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_card_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open AdmissibleUnits
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : QuotCyclic := by
  unfold QuotCyclic
  intro n
  have hsq : (-1 : (ZMod (2 ^ (n + 2)))ˣ) ^ 2 = 1 := neg_one_sq
  have h5 : orderOf (QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ))
      (u5 (n + 2))) = 2 ^ n := by
    rw [orderOf_mk_eq hsq (neg_not_mem_five n), orderOf_five_units_two_pow n]
  refine ⟨isCyclic_of_orderOf_eq_card _ (h5.trans (card_quot n).symm), card_quot n, h5, ?_⟩
  cases n with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff, QuotientGroup.eq_one_iff]
    have h3 : u3 (0 + 2) = -1 := by
      unfold u3
      apply Units.ext
      rw [ZMod.coe_unitOfCoprime, Units.val_neg, Units.val_one]
      decide
    rw [h3]
    exact Subgroup.mem_zpowers _
  | succ n =>
    show orderOf (QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 3)))ˣ))
      (u3 (n + 3))) = 2 ^ (n + 1)
    rw [orderOf_mk_eq neg_one_sq (neg_not_mem_three n)]
    exact orderOf_three_units_two_pow n
end Formalism.TwoAdicCyclotomicDecomposition
