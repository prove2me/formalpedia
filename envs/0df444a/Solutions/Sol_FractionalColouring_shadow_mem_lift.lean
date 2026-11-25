-- Prove2me | solution 1 for FractionalColouring.shadow_mem_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:35:06.533521+00:00
-- url     : https://prove2.me/submissions/141b7047-e278-407c-956d-683af3614105

module
public import Definitions.Def_FractionalLib_Basic
public import Definitions.Def_Mycielski_Basic
public import Definitions.Def_FractionalLib_LarsenProppUllman
public import Theorems.Thm_FractionalColouring_original_mem_lift
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

set_option autoImplicit true
@[expose] public section
public section
open Finset hiding shadow
open Mycielski
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
omit [Fintype V]
namespace FractionalColouring
theorem _root_.solution {s : Finset V} {v : V} : shadow v ∈ lift s ↔ v ∈ s := by
  simp [lift, original, shadow]
end FractionalColouring
