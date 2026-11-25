-- Prove2me | solution 1 for GalvinMultigraph.colorable_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:28:13.585884+00:00
-- url     : https://prove2.me/submissions/4041cb7b-ce6e-4277-88da-d54459363d7b

module
public import Definitions.Def_GalvinMultigraph_Gadget
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinMultigraph_Main
public import Theorems.Thm_GalvinMultigraph_galvin
public import Theorems.Thm_GalvinMultigraph_maxDegree_le_of_proper
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_aEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_bEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_innerEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_rowEdge
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
theorem _root_.solution [Fintype A] [Fintype B] [Finite E]
    (a : E → A) (b : E → B) (k : ℕ) :
    (∃ c : E → Fin k, Proper a b c) ↔ maxDegree a b ≤ k := by
  constructor
  · rintro ⟨c, hc⟩
    simpa using maxDegree_le_of_proper a b c hc
  · intro hk
    obtain ⟨c, _, hc⟩ := galvin a b (fun _ => (univ : Finset (Fin k))) (by intro e; simpa using hk)
    exact ⟨c, hc⟩
end GalvinMultigraph
