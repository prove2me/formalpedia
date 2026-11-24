-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.orderOf_mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:46.508659+00:00
-- url     : https://prove2.me/submissions/73ed18b4-566a-456d-a1d1-97179a8e3281

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_zpowers_sq

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
theorem _root_.solution {G : Type*} [CommGroup G] [Finite G] {x g : G} (hg : g ^ 2 = 1)
    (hx : g ∉ Subgroup.zpowers x) :
    orderOf (QuotientGroup.mk (s := Subgroup.zpowers g) x) = orderOf x := by
  apply Nat.dvd_antisymm
  · exact orderOf_map_dvd (QuotientGroup.mk' _) x
  · apply orderOf_dvd_of_pow_eq_one
    have h1 : (QuotientGroup.mk (s := Subgroup.zpowers g) x) ^
        orderOf (QuotientGroup.mk (s := Subgroup.zpowers g) x) = 1 := pow_orderOf_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    rcases zpowers_sq hg h1 with h2 | h2
    · exact h2
    · exact absurd (by rw [← h2]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _) hx
end Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
