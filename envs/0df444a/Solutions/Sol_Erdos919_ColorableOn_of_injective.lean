-- Prove2me | solution 1 for Erdos919.ColorableOn.of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:33:19.889183+00:00
-- url     : https://prove2.me/submissions/4817715e-39a0-4dec-bf79-1bd614a98f18

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
namespace ColorableOn
theorem _root_.solution {V : Type*} {G : SimpleGraph V} {X : Set V} {α β : Type*}
    (h : ColorableOn G X α) (f : α → β) (hf : Function.Injective f) : ColorableOn G X β := by
  obtain ⟨c, hc⟩ := h
  exact ⟨f ∘ c, fun x hx y hy hxy e => hc x hx y hy hxy (hf e)⟩
end ColorableOn
end Erdos919
