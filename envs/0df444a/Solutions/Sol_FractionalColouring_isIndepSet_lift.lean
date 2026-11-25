-- Prove2me | solution 1 for FractionalColouring.isIndepSet_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:49:42.902568+00:00
-- url     : https://prove2.me/submissions/00ad6808-1977-40b2-ab8e-15a8efa449f3

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
    (graph G).IsIndepSet ((lift s : Finset (Vertex V)) : Set (Vertex V)) := by
  intro u hu u' hu' huu'
  simp only [lift, coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe] at hu hu'
  rcases hu with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;> rcases hu' with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · exact hs hv hw (fun h => huu' (by rw [h]))
  · simp only [original_adj_shadow]
    by_cases hvw : v = w
    · subst hvw; exact G.irrefl
    · exact hs hv hw hvw
  · simp only [shadow_adj_original]
    by_cases hvw : v = w
    · subst hvw; exact G.irrefl
    · exact hs hv hw hvw
  · exact not_shadow_adj_shadow G v w
end FractionalColouring
