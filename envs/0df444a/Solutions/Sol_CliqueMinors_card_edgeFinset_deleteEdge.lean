-- Prove2me | solution 1 for CliqueMinors.card_edgeFinset_deleteEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:41:57.576371+00:00
-- url     : https://prove2.me/submissions/86793095-0c69-414a-8407-187aaa83080e

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
namespace CliqueMinors
theorem _root_.solution {G : SimpleGraph V} {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    (G.deleteEdges {e}).edgeFinset.card + 1 = G.edgeFinset.card := by
  have h : (G.deleteEdges {e}).edgeFinset = G.edgeFinset.erase e := by
    ext f
    simp only [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff,
      Finset.mem_erase]
    tauto
  rw [h, Finset.card_erase_of_mem he]
  have := Finset.card_pos.2 ⟨e, he⟩
  omega
end CliqueMinors
