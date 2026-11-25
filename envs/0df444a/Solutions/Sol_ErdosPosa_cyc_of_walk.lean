-- Prove2me | solution 1 for ErdosPosa.cyc_of_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:22:10.307676+00:00
-- url     : https://prove2.me/submissions/507bf738-b77b-4d6a-89d3-427b5532c24b

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Theorems.Thm_ErdosPosa_cyc_iff

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution {H : SimpleGraph V} {S : Set V} {u v : V} (huv : H.Adj u v) (p : H.Walk u v)
    (hS : ∀ x ∈ p.support, x ∈ S) (he : s(u, v) ∉ p.edges) : Cyc H S := by
  rw [cyc_iff]
  refine ⟨u, v, ⟨huv, hS _ p.start_mem_support, hS _ p.end_mem_support⟩, ⟨p.transfer _ ?_⟩⟩
  intro e hep
  have hHe := p.edges_subset_edgeSet hep
  induction e using Sym2.ind with
  | _ a b =>
    rw [edgeSet_deleteEdges, Set.mem_sdiff]
    refine ⟨?_, ?_⟩
    · exact ⟨hHe, hS _ (p.fst_mem_support_of_mem_edges hep),
        hS _ (p.snd_mem_support_of_mem_edges hep)⟩
    · rintro h
      rw [Set.mem_singleton_iff] at h
      exact he (h ▸ hep)
end ErdosPosa
