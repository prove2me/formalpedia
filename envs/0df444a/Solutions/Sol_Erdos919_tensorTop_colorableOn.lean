-- Prove2me | solution 1 for Erdos919.tensorTop_colorableOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:33:46.26285+00:00
-- url     : https://prove2.me/submissions/3b6279bf-a6cc-458f-a1b0-9a7722376128

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {V T α : Type*} (H : SimpleGraph V) (X : Set (V × T))
    (h : ColorableOn H (Prod.fst '' X) α) : ColorableOn (tensorTop H T) X α := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun p => c p.1, fun x hx y hy hxy => hc _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ (tensorTop_adj.1 hxy).1⟩
end Erdos919
