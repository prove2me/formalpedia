-- Prove2me | solution 1 for C6BipartiteDomination.paper11AllRepairOwners_subset_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:58:28.293208+00:00
-- url     : https://prove2.me/submissions/f2a0bbb9-a3c7-43ab-a610-e1d34f14bcac

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2

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
    paper11AllRepairOwners G D hCan hmax ⊆ BPart G D := by
  intro u hu
  rcases Finset.mem_union.mp hu with hu | hu
  · exact (Finset.mem_filter.mp hu).1
  · exact (Finset.mem_filter.mp hu).1
end C6BipartiteDomination
