-- Prove2me | solution 1 for C6BipartiteDomination.paper11AllCompensation_charge_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:00:42.373227+00:00
-- url     : https://prove2.me/submissions/01f39147-a081-4cef-9f2e-45391cae45c3

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11OwnerCompensation_charge_four
import Theorems.Thm_C6BipartiteDomination_paper11AllRepairOwners_subset_B

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {q : V}
    (hq : q ∈ paper11AllCompensation G D hCan hmax) :
    externalCharge G D q = 4 := by
  obtain ⟨u, hu, hq⟩ := Finset.mem_biUnion.mp hq
  exact paper11OwnerCompensation_charge_four G hCan hmax
    (paper11AllRepairOwners_subset_B G hCan hmax hu) hq
end C6BipartiteDomination
