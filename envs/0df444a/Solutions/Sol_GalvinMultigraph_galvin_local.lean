-- Prove2me | solution 1 for GalvinMultigraph.galvin_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:19:55.887426+00:00
-- url     : https://prove2.me/submissions/8634e0b1-eb1c-4c0a-a5b4-f1ecf7030491

module
public import Definitions.Def_GalvinMultigraph_Main
public import Definitions.Def_GalvinMultigraph_Local_Main
public import Definitions.Def_GalvinMultigraph_Local_Bridge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_aEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_bEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_innerEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_rowEdge
public import Theorems.Thm_GalvinMultigraph_Local_galvin_bkw_local
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
    (a : E → A) (b : E → B) (L : E → Finset Color)
    (hL : ∀ e, max (Nat.card {f // a f = a e}) (Nat.card {f // b f = b e}) ≤ (L e).card) :
    ∃ c : E → Color, (∀ e, c e ∈ L e) ∧ Proper a b c := by
  classical
  let _ := Fintype.ofFinite A
  let _ := Fintype.ofFinite B
  let _ := Fintype.ofFinite E
  -- number the colours occurring in the lists
  set S : Finset Color := univ.biUnion L with hS
  let num : S ≃ Fin S.card := S.equivFin
  let enc : Color → ℕ := fun x => if h : x ∈ S then (num ⟨x, h⟩ : ℕ) else 0
  have hLS : ∀ e, L e ⊆ S := fun e x hx => mem_biUnion.2 ⟨e, mem_univ e, hx⟩
  have henc : ∀ x ∈ S, ∀ y ∈ S, enc x = enc y → x = y := by
    intro x hx y hy h
    simp only [enc, dif_pos hx, dif_pos hy] at h
    exact congrArg Subtype.val (num.injective (Fin.ext h))
  let L' : E → Finset ℕ := fun e => (L e).image enc
  have hcard : ∀ e, (L' e).card = (L e).card := fun e =>
    card_image_of_injOn fun x hx y hy h => henc x (hLS e hx) y (hLS e hy) h
  have hdA : ∀ x, Local.degL a x = Nat.card {f // a f = x} := fun x => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have hdB : ∀ y, Local.degR b y = Nat.card {f // b f = y} := fun y => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  obtain ⟨φ, hφL, hφ⟩ := Local.galvin_bkw_local a b L' fun e => by
    rw [hcard, hdA, hdB]
    exact hL e
  have hdec : ∀ e, ∃ x ∈ L e, enc x = φ e := fun e => mem_image.1 (hφL e)
  choose c hcL hce using hdec
  refine ⟨c, hcL, fun e f hef hab hc => hφ e f hef hab ?_⟩
  rw [← hce e, ← hce f, hc]
end GalvinMultigraph
