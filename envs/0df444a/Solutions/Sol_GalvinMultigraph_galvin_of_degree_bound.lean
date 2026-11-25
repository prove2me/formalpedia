-- Prove2me | solution 1 for GalvinMultigraph.galvin_of_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:22:07.280587+00:00
-- url     : https://prove2.me/submissions/e757b25b-e520-44bb-b415-66f8870afb24

module
public import Definitions.Def_GalvinMultigraph_Gadget
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinMultigraph_Main
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_aEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_bEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_card
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_innerEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_rowEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_maxDegree_le
public import Theorems.Thm_GalvinMultigraph_Gadget_terminal_agreement
public import Theorems.Thm_GalvinMultigraph_Gadget_terminal_proper
public import Theorems.Thm_Galvin_galvin
public import Theorems.Thm_LeanPool_Vizing_PEC_kempeSwap_col
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_right
attribute [local simp] GalvinMultigraph.Gadget.lists_aEdge
attribute [local simp] GalvinMultigraph.Gadget.lists_bEdge
attribute [local simp] GalvinMultigraph.Gadget.lists_innerEdge
attribute [local simp] GalvinMultigraph.Gadget.lists_rowEdge
attribute [local simp] LeanPool.Vizing.PEC.kempeSwap_col
attribute [local simp] LeanPool.Vizing.PEC.setEdge_col
attribute [local simp] LeanPool.Vizing.PEC.updFun_left
attribute [local simp] LeanPool.Vizing.PEC.updFun_right



set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph
open Finset
variable {A B E Color : Type*}
namespace GalvinMultigraph
theorem _root_.solution [Finite A] [Finite B] [Finite E]
    (a : E → A) (b : E → B) (k : ℕ)
    (ha : ∀ x, Nat.card {e // a e = x} ≤ k)
    (hb : ∀ y, Nat.card {e // b e = y} ≤ k)
    (L : E → Finset Color) (hL : ∀ e, k ≤ (L e).card) :
    ∃ c : E → Color, (∀ e, c e ∈ L e) ∧ Proper a b c := by
  classical
  let _ := Fintype.ofFinite A
  let _ := Fintype.ofFinite B
  let _ := Fintype.ofFinite E
  cases isEmpty_or_nonempty E with
  | inl hE =>
    exact ⟨isEmptyElim, fun e => isEmptyElim e, fun e => isEmptyElim e⟩
  | inr hE =>
    have hk : k ≠ 0 := by
      intro hk
      obtain ⟨e⟩ := hE
      have h := ha (a e)
      have : Nonempty {f : E // a f = a e} := ⟨⟨e, rfl⟩⟩
      rw [hk, Nat.card_eq_fintype_card] at h
      have := Fintype.card_pos (α := {f : E // a f = a e})
      omega
    have : NeZero k := ⟨hk⟩
    choose P hsub hP using fun e => Finset.exists_subset_card_eq (hL e)
    let G := Gadget.graph (k := k) a b
    have hdeg : G.maxDegree ≤ k := Gadget.maxDegree_le a b ha hb
    obtain ⟨col, hcol⟩ := Galvin.galvin G ⟨Gadget.coloring a b⟩ (Gadget.lists a b P)
      (fun f => by rw [Gadget.lists_card a b P hP f]; exact hdeg)
    refine ⟨fun e => col (Gadget.aEdge a b e), ?_, ?_⟩
    · intro e
      apply hsub e
      simpa using hcol (Gadget.aEdge a b e)
    · exact Gadget.terminal_proper a b col
        (fun e => Gadget.terminal_agreement a b P col hcol e (hP e))
end GalvinMultigraph
