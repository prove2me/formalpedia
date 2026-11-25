-- Prove2me | solution 1 for Galvin.eq_of_colour_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:52:25.706089+00:00
-- url     : https://prove2.me/submissions/55945659-f8b3-434b-b2e9-4ee69b62462a

module
public import Definitions.Def_GalvinLib_GaleShapley
public import Definitions.Def_GalvinLib_Kernel
public import Mathlib.Order.Interval.Finset.Fin
public import Definitions.Def_GalvinLib_Orientation
public import Theorems.Thm_Galvin_lineGraph_adj_iff_ends

set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace Galvin
theorem _root_.solution (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    {e f : G.edgeSet} (hφ : φ e = φ f) (h : endA c e = endA c f ∨ endB c e = endB c f) :
    e = f := by
  by_contra hne
  exact φ.valid ((lineGraph_adj_iff_ends c).2 ⟨hne, h⟩) hφ
end Galvin
