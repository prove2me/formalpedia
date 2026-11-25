-- Prove2me | solution 1 for ErdosPosa.MinCyc.reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:22:13.135019+00:00
-- url     : https://prove2.me/submissions/2b6aae11-385f-4695-b8dc-a416aa93f483

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Theorems.Thm_ErdosPosa_cyc_iff
public import Theorems.Thm_ErdosPosa_deleteEdges_adj_iff
public import Theorems.Thm_ErdosPosa_support_subset_of_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
namespace MinCyc
theorem _root_.solution {H : SimpleGraph V} {T : Set V} (h : MinCyc H T) {a b : V} (ha : a ∈ T)
    (hb : b ∈ T) : (restr H T).Reachable a b := by
  classical
  have h1 := h.1
  rw [cyc_iff] at h1
  obtain ⟨u, v, huv, ⟨p⟩⟩ := h1
  let T' : Set V := {x | x ∈ p.support}
  have hT'T : T' ⊆ T := by
    intro x hx
    refine support_subset_of_adj (T := T) ?_ p huv.2.1 x hx
    intro a b hab
    rw [deleteEdges_adj_iff] at hab
    exact hab.1.2.2
  have hcyc : Cyc H T' := by
    rw [cyc_iff]
    refine ⟨u, v, ⟨huv.1, p.start_mem_support, p.end_mem_support⟩, ⟨p.transfer _ ?_⟩⟩
    intro e hep
    have hHe := p.edges_subset_edgeSet hep
    induction e using Sym2.ind with
    | _ a b =>
      rw [edgeSet_deleteEdges, Set.mem_sdiff] at hHe ⊢
      exact ⟨⟨hHe.1.1, p.fst_mem_support_of_mem_edges hep, p.snd_mem_support_of_mem_edges hep⟩,
        hHe.2⟩
  have heq := h.2 T' hT'T hcyc
  have hreach : ∀ x ∈ T, (restr H T).Reachable u x := by
    intro x hx
    rw [← heq] at hx
    exact ⟨(p.takeUntil x hx).mapLe (deleteEdges_le _)⟩
  exact (hreach a ha).symm.trans (hreach b hb)
end MinCyc
end ErdosPosa
