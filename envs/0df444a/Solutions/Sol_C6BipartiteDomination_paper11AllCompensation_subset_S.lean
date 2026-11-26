-- Prove2me | solution 1 for C6BipartiteDomination.paper11AllCompensation_subset_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:16.805859+00:00
-- url     : https://prove2.me/submissions/56907a2a-36a9-4ff6-a8fc-ca45cf46e565

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11OwnerCompensation_subset_S
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
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11AllCompensation G D hCan hmax ⊆ SPart G D := by
  intro q hq
  obtain ⟨u, hu, hq⟩ := Finset.mem_biUnion.mp hq
  exact paper11OwnerCompensation_subset_S G hCan hmax
    (paper11AllRepairOwners_subset_B G hCan hmax hu) hq
end C6BipartiteDomination
