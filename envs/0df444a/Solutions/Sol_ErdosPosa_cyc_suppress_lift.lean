-- Prove2me | solution 1 for ErdosPosa.cyc_suppress_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:25:08.391543+00:00
-- url     : https://prove2.me/submissions/80d5e03e-9899-409e-9c7b-819598cfd1c5

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMoore
public import Definitions.Def_ErdosPosaLib_EPShort
public import Theorems.Thm_ErdosPosa_suppress_adj
public import Theorems.Thm_ErdosPosa_MinCyc_reachable
public import Theorems.Thm_ErdosPosa_cyc_iff
public import Theorems.Thm_ErdosPosa_deleteEdges_adj_iff
public import Theorems.Thm_ErdosPosa_reach_transfer


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution {H : SimpleGraph V} {x a b : V} (hxa : H.Adj x a) (hxb : H.Adj x b)
    {S : Set V} (h : Cyc (suppress H x a b) S) : Cyc H (insert x S) := by
  rw [cyc_iff] at h ⊢
  obtain ⟨u, v, ⟨huv, hu, hv⟩, hr⟩ := h
  have hxA : x ≠ a := hxa.ne
  have hxB : x ≠ b := hxb.ne
  rw [suppress_adj] at huv
  have key : a ≠ b → ((restr (suppress H x a b) S).deleteEdges {s(a, b)}).Reachable a b →
      b ∈ S → ((restr H (insert x S)).deleteEdges {s(x, a)}).Reachable x a := by
    intro hab hr hb
    have hxb' : ((restr H (insert x S)).deleteEdges {s(x, a)}).Adj x b := by
      rw [deleteEdges_adj_iff]
      refine ⟨⟨hxb, Set.mem_insert _ _, Set.mem_insert_of_mem _ hb⟩, ?_⟩
      intro he
      rw [Sym2.eq_iff] at he
      rcases he with ⟨-, h1⟩ | ⟨h1, -⟩
      · exact hab h1.symm
      · exact hxA h1
    refine hxb'.reachable.trans ?_
    have tr := reach_transfer (G2 := (restr H (insert x S)).deleteEdges {s(x, a)}) id ?_ hr
    · exact tr.symm
    intro c d hcd
    rw [deleteEdges_adj_iff] at hcd
    obtain ⟨⟨hcd, hc, hd⟩, hne⟩ := hcd
    rw [suppress_adj] at hcd
    rcases hcd with ⟨hcd, hcx, hdx⟩ | ⟨hca, hdb, -⟩ | ⟨hcb, hda, -⟩
    · apply Adj.reachable
      rw [deleteEdges_adj_iff]
      refine ⟨⟨hcd, Set.mem_insert_of_mem _ hc, Set.mem_insert_of_mem _ hd⟩, ?_⟩
      intro he
      rw [Sym2.eq_iff] at he
      rcases he with ⟨h1, -⟩ | ⟨-, h1⟩
      · exact hcx h1
      · exact hdx h1
    · exact absurd (by rw [hca, hdb]) hne
    · exact absurd (by rw [hcb, hda, Sym2.eq_swap]) hne
  rcases huv with ⟨huv, hux, hvx⟩ | ⟨hua, hvb, hab⟩ | ⟨hub, hva, hab⟩
  · refine ⟨u, v, ⟨huv, Set.mem_insert_of_mem _ hu, Set.mem_insert_of_mem _ hv⟩, ?_⟩
    refine reach_transfer (G2 := (restr H (insert x S)).deleteEdges {s(u, v)}) id ?_ hr
    intro c d hcd
    rw [deleteEdges_adj_iff] at hcd
    obtain ⟨⟨hcd, hc, hd⟩, hne⟩ := hcd
    rw [suppress_adj] at hcd
    have hxe : ∀ y, s(x, y) ≠ s(u, v) := by
      intro y he
      rw [Sym2.eq_iff] at he
      rcases he with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hux h1.symm
      · exact hvx h1.symm
    have hxe' : ∀ y, s(y, x) ≠ s(u, v) := by
      intro y he; rw [Sym2.eq_swap] at he; exact hxe y he
    rcases hcd with ⟨hcd, hcx, hdx⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
    · apply Adj.reachable
      rw [deleteEdges_adj_iff]
      exact ⟨⟨hcd, Set.mem_insert_of_mem _ hc, Set.mem_insert_of_mem _ hd⟩, hne⟩
    · have h1 : ((restr H (insert x S)).deleteEdges {s(u, v)}).Adj c x := by
        rw [deleteEdges_adj_iff]
        exact ⟨⟨hxa.symm, Set.mem_insert_of_mem _ hc, Set.mem_insert _ _⟩, hxe' _⟩
      have h2 : ((restr H (insert x S)).deleteEdges {s(u, v)}).Adj x d := by
        rw [deleteEdges_adj_iff]
        exact ⟨⟨hxb, Set.mem_insert _ _, Set.mem_insert_of_mem _ hd⟩, hxe _⟩
      exact h1.reachable.trans h2.reachable
    · have h1 : ((restr H (insert x S)).deleteEdges {s(u, v)}).Adj c x := by
        rw [deleteEdges_adj_iff]
        exact ⟨⟨hxb.symm, Set.mem_insert_of_mem _ hc, Set.mem_insert _ _⟩, hxe' _⟩
      have h2 : ((restr H (insert x S)).deleteEdges {s(u, v)}).Adj x d := by
        rw [deleteEdges_adj_iff]
        exact ⟨⟨hxa, Set.mem_insert _ _, Set.mem_insert_of_mem _ hd⟩, hxe _⟩
      exact h1.reachable.trans h2.reachable
  · rw [hua, hvb] at hr
    rw [hua] at hu
    rw [hvb] at hv
    exact ⟨x, a, ⟨hxa, Set.mem_insert _ _, Set.mem_insert_of_mem _ hu⟩, key hab hr hv⟩
  · rw [hub, hva, Sym2.eq_swap] at hr
    rw [hva] at hv
    rw [hub] at hu
    exact ⟨x, a, ⟨hxa, Set.mem_insert _ _, Set.mem_insert_of_mem _ hv⟩, key hab hr.symm hu⟩
end ErdosPosa
