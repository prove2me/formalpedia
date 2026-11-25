-- Prove2me | solution 1 for Galvin.dinitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:22:44.891505+00:00
-- url     : https://prove2.me/submissions/5ababb49-e06c-4bd7-b65a-c058a83b48df

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Definitions.Def_Konig_Basic
public import Definitions.Def_GalvinLib_Orientation
public import Definitions.Def_GalvinLib_Galvin
public import Theorems.Thm_Galvin_galvin
public import Theorems.Thm_LeanPool_Vizing_PEC_Extends_trans
public import Theorems.Thm_LeanPool_Vizing_PEC_kempeSwap_col
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_right
attribute [local simp] LeanPool.Vizing.PEC.kempeSwap_col
attribute [local simp] LeanPool.Vizing.PEC.setEdge_col
attribute [local simp] LeanPool.Vizing.PEC.updFun_left
attribute [local simp] LeanPool.Vizing.PEC.updFun_right



set_option autoImplicit true
@[expose] public section
public section
open Galvin
namespace Galvin
theorem _root_.solution {Symbol : Type*} (n : ℕ) (lists : Fin n → Fin n → Finset Symbol)
    (hLists : ∀ i j, n ≤ (lists i j).card) :
    ∃ f : Fin n → Fin n → Symbol, (∀ i j, f i j ∈ lists i j) ∧
      (∀ i j j', j ≠ j' → f i j ≠ f i j') ∧ (∀ i i' j, i ≠ i' → f i j ≠ f i' j) := by
  classical
  let G := completeBipartiteGraph (Fin n) (Fin n)
  have hG : G.Colorable 2 :=
    ⟨SimpleGraph.Coloring.mk (fun v => Sum.elim (fun _ => 0) (fun _ => 1) v) (by
      rintro (i | i) (j | j) h <;> simp [G] at h ⊢)⟩
  have hdeg : G.maxDegree ≤ n := by
    refine G.maxDegree_le_of_forall_degree_le n fun v => ?_
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    rcases v with i | i
    · calc (G.neighborFinset (Sum.inl i)).card
            ≤ (Finset.univ.image (Sum.inr : Fin n → _)).card :=
            Finset.card_le_card fun w hw => by
              rcases w with j | j <;> simp [G] at hw ⊢
        _ ≤ n := Finset.card_image_le.trans (by simp)
    · calc (G.neighborFinset (Sum.inr i)).card
            ≤ (Finset.univ.image (Sum.inl : Fin n → _)).card :=
            Finset.card_le_card fun w hw => by
              rcases w with j | j <;> simp [G] at hw ⊢
        _ ≤ n := Finset.card_image_le.trans (by simp)
  let cell : Fin n ⊕ Fin n → Fin n ⊕ Fin n → Finset Symbol := fun a b =>
    match a, b with
    | Sum.inl i, Sum.inr j => lists i j
    | Sum.inr j, Sum.inl i => lists i j
    | _, _ => ∅
  have hcell : ∀ a b, cell a b = cell b a := by
    rintro (i | i) (j | j) <;> rfl
  let L : G.edgeSet → Finset Symbol := fun e => Sym2.lift ⟨cell, hcell⟩ e
  have hL : ∀ e, G.maxDegree ≤ (L e).card := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
    refine hdeg.trans ?_
    rcases a with i | i <;> rcases b with j | j <;>
      simp [G, L, cell, Sym2.lift_mk, hLists] at he ⊢
  obtain ⟨col, hcol⟩ := galvin G hG L hL
  have hadj : ∀ i j, G.Adj (Sum.inl i) (Sum.inr j) := fun i j => by simp [G]
  let edge : Fin n → Fin n → G.edgeSet := fun i j => ⟨s(Sum.inl i, Sum.inr j), hadj i j⟩
  refine ⟨fun i j => col (edge i j), fun i j => ?_, fun i j j' hjj => ?_, fun i i' j hii => ?_⟩
  · simpa [L, edge, cell, Sym2.lift_mk] using hcol (edge i j)
  · refine col.valid ?_
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨fun h => hjj ?_, Sum.inl i, by simp [edge], by simp [edge]⟩
    simpa [edge] using congrArg Subtype.val h
  · refine col.valid ?_
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨fun h => hii ?_, Sum.inr j, by simp [edge], by simp [edge]⟩
    simpa [edge] using congrArg Subtype.val h
end Galvin
