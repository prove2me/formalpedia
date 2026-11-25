-- Prove2me | solution 1 for ErdosPosa.not_isAcyclic_induce_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:23:20.415745+00:00
-- url     : https://prove2.me/submissions/1bca01fc-a697-490c-8040-536a1e32fdf0

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Theorems.Thm_ErdosPosa_restr_adj
public import Theorems.Thm_ErdosPosa_reach_transfer
public import Theorems.Thm_ErdosPosa_cyc_iff
public import Theorems.Thm_ErdosPosa_deleteEdges_adj_iff
attribute [local simp] ErdosPosa.restr_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution {G : SimpleGraph V} {S : Set V} :
    ¬ (G.induce S).IsAcyclic ↔ Cyc G S := by
  constructor
  · intro h hac
    apply h
    refine hac.comap (G := G.induce S)
      ⟨fun x => x.1, fun {a b} hab => (restr_adj.2 ⟨hab, a.2, b.2⟩ : (restr G S).Adj a b)⟩ ?_
    intro a b hab; exact Subtype.ext hab
  · intro h hac
    rw [cyc_iff] at h
    obtain ⟨u, v, huv, hr⟩ := h
    rw [isAcyclic_iff_forall_adj_isBridge] at hac
    have hb := hac (v := ⟨u, huv.2.1⟩) (w := ⟨v, huv.2.2⟩) huv.1
    rw [isBridge_iff] at hb
    apply hb
    classical
    let f : V → S := fun x => if hx : x ∈ S then ⟨x, hx⟩ else ⟨u, huv.2.1⟩
    have hfu : f u = ⟨u, huv.2.1⟩ := by simp [f, huv.2.1]
    have hfv : f v = ⟨v, huv.2.2⟩ := by simp [f, huv.2.2]
    have := reach_transfer (G2 := (G.induce S).deleteEdges {s(⟨u, huv.2.1⟩, ⟨v, huv.2.2⟩)})
      f ?_ hr
    · rwa [hfu, hfv] at this
    intro a b hab
    rw [deleteEdges_adj_iff] at hab
    obtain ⟨⟨hab, ha, hb⟩, hne⟩ := hab
    apply Adj.reachable
    rw [deleteEdges_adj_iff]
    simp only [f, ha, hb, dite_true]
    refine ⟨hab, ?_⟩
    intro heq
    apply hne
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Subtype.mk.injEq, Prod.swap_prod_mk] at heq ⊢
    exact heq
end ErdosPosa
