-- Prove2me | solution 1 for Erdos919.colorableOn_iff_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:33:15.660487+00:00
-- url     : https://prove2.me/submissions/f958758e-926e-45df-9c37-c3acbcec4130

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
theorem _root_.solution {V : Type*} (G : SimpleGraph V) (X : Set V) (α : Type*)
    [Nonempty α] : ColorableOn G X α ↔ Nonempty ((G.induce X).Coloring α) := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk (fun x => c x) (fun {x y} h => hc x x.2 y y.2 (by simpa using h))⟩
  · rintro ⟨c⟩
    refine ⟨fun v => if h : v ∈ X then c ⟨v, h⟩ else Classical.arbitrary α, ?_⟩
    intro x hx y hy hxy
    simp only [hx, hy, dite_true]
    exact c.valid (by simpa using hxy)
end Erdos919
