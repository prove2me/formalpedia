-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.card_GG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:42:46.908929+00:00
-- url     : https://prove2.me/submissions/adae5f81-41e1-4da2-bc9a-e9cb14c555aa

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_card_GamE
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_resMap_surj
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_card_GalL__249609

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {s m : ℕ} (h : s ≤ m) : Nat.card (GG h) = 2 ^ (m - s + 1) := by
  have hs : Function.Surjective
      ((QuotientGroup.mk' (Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2)))).comp (resMap h)) :=
    (QuotientGroup.mk'_surjective _).comp (resMap_surj h)
  have e := QuotientGroup.quotientKerEquivOfSurjective _ hs
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((QuotientGroup.mk' (Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2)))).comp (resMap h)).ker
  rw [Nat.card_congr e.toEquiv, card_GalL, card_GamE] at h1
  have h3 : (2:ℕ) ^ (m + 3) = 2 ^ (s + 2) * 2 ^ (m - s + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h3] at h1
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm
end Formalism.TwoAdicCyclotomicDecomposition
