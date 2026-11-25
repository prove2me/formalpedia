-- Prove2me | solution 1 for FractionalColouring.isIndepSet_liftApex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:49:45.438258+00:00
-- url     : https://prove2.me/submissions/dd87376b-9a32-4a13-8113-0bb2e2ca1d21

module
public import Definitions.Def_FractionalLib_Basic
public import Definitions.Def_Mycielski_Basic
public import Definitions.Def_FractionalLib_LarsenProppUllman
public import Theorems.Thm_FractionalColouring_original_mem_lift
public import Theorems.Thm_FractionalColouring_shadow_mem_lift
public import Theorems.Thm_FractionalColouring_none_not_mem_lift
public import Theorems.Thm_FractionalColouring_original_mem_liftApex
public import Theorems.Thm_FractionalColouring_shadow_not_mem_liftApex
public import Theorems.Thm_FractionalColouring_none_mem_liftApex
public import Theorems.Thm_FractionalColouring_original_not_mem_shadows
public import Theorems.Thm_FractionalColouring_shadow_mem_shadows
public import Theorems.Thm_FractionalColouring_none_not_mem_shadows
public import Theorems.Thm_FiniteLP_toE_apply
public import Theorems.Thm_Mycielski_apex_adj_shadow
public import Theorems.Thm_Mycielski_not_shadow_adj_shadow
public import Theorems.Thm_Mycielski_original_adj_original
public import Theorems.Thm_Mycielski_original_adj_shadow
public import Theorems.Thm_Mycielski_shadow_adj_apex
public import Theorems.Thm_Mycielski_shadow_adj_original
attribute [local simp] FiniteLP.toE_apply
attribute [local simp] Mycielski.apex_adj_shadow
attribute [local simp] Mycielski.not_shadow_adj_shadow
attribute [local simp] Mycielski.original_adj_original
attribute [local simp] Mycielski.original_adj_shadow
attribute [local simp] Mycielski.shadow_adj_apex
attribute [local simp] Mycielski.shadow_adj_original


attribute [local simp] FractionalColouring.original_mem_lift
attribute [local simp] FractionalColouring.shadow_mem_lift
attribute [local simp] FractionalColouring.none_not_mem_lift
attribute [local simp] FractionalColouring.original_mem_liftApex
attribute [local simp] FractionalColouring.shadow_not_mem_liftApex
attribute [local simp] FractionalColouring.none_mem_liftApex
attribute [local simp] FractionalColouring.original_not_mem_shadows
attribute [local simp] FractionalColouring.shadow_mem_shadows
attribute [local simp] FractionalColouring.none_not_mem_shadows

set_option autoImplicit true
@[expose] public section
public section
open Finset hiding shadow
open Mycielski
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}
namespace FractionalColouring
theorem _root_.solution {s : Finset V} (hs : G.IsIndepSet (s : Set V)) :
    (graph G).IsIndepSet ((liftApex s : Finset (Vertex V)) : Set (Vertex V)) := by
  intro u hu u' hu' huu'
  simp only [liftApex, coe_insert, coe_image, Set.mem_insert_iff, Set.mem_image, mem_coe] at hu hu'
  rcases hu with rfl | ⟨v, hv, rfl⟩ <;> rcases hu' with rfl | ⟨w, hw, rfl⟩
  · exact absurd rfl huu'
  · simp [graph, Mycielski.Adj, original]
  · simp [graph, Mycielski.Adj, original]
  · exact hs hv hw (fun h => huu' (by rw [h]))
end FractionalColouring
