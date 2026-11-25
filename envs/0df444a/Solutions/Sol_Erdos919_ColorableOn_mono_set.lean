-- Prove2me | solution 1 for Erdos919.ColorableOn.mono_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:25:49.3633+00:00
-- url     : https://prove2.me/submissions/656a8595-64c7-4c98-87dc-186b165be0d5

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
theorem _root_.solution {V : Type*} {G : SimpleGraph V} {X Y : Set V} {α : Type*}
    (h : ColorableOn G Y α) (hXY : X ⊆ Y) : ColorableOn G X α := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun x hx y hy => hc x (hXY hx) y (hXY hy)⟩
end ColorableOn
end Erdos919
