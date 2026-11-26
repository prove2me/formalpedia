-- Prove2me | solution 1 for C6BipartiteDomination.bpart_zpart_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:00.076917+00:00
-- url     : https://prove2.me/submissions/f33cdef1-9866-471a-a036-25ecca39a28a

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
import Theorems.Thm_C6BipartiteDomination_zpart_subset_selected

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) :
    D = BPart G D ∪ ZPart G D := by
  classical
  ext v
  constructor
  · intro hvD
    by_cases hvZ : v ∈ ZPart G D
    · exact Finset.mem_union_right _ hvZ
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvD, hvZ⟩)
  · intro hv
    rcases Finset.mem_union.mp hv with hvB | hvZ
    · exact (Finset.mem_sdiff.mp (by simpa [BPart] using hvB)).1
    · exact zpart_subset_selected G D hvZ
end C6BipartiteDomination
