-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.unitsTwoPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:02:35.514052+00:00
-- url     : https://prove2.me/submissions/755c5659-fa80-417b-8171-d2aa75e22283

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_neg_not_mem_five
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_neg_not_mem_three
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_card_units
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_orderOf_five_units_two_pow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_orderOf_three_units_two_pow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_inj

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
theorem _root_.solution : UnitsTwoPow := by
  unfold UnitsTwoPow
  intro n
  refine ⟨card_units (n + 2), orderOf_five_units_two_pow (n + 1), orderOf_three_units_two_pow n, neg_not_mem_five (n + 1),
    neg_not_mem_three n, ?_⟩
  intro u
  have hc : Nat.card (ZMod (2 ^ (n + 3)))ˣ = 2 ^ (n + 2) := card_units (n + 2)
  have hcard : Fintype.card (Bool × Fin (2 ^ (n + 1))) = Fintype.card (ZMod (2 ^ (n + 3)))ˣ := by
    rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, ← Nat.card_eq_fintype_card, hc]
    ring
  have hbij := (Fintype.bijective_iff_injective_and_card _).mpr ⟨inj n, hcard⟩
  obtain ⟨p, hp⟩ := hbij.2 u
  exact ⟨p, hp.symm, fun q hq => hbij.1 (hq.symm.trans hp.symm)⟩
end Formalism.TwoAdicCyclotomicDecomposition
