-- Prove2me | solution 1 for Galvin.lineGraph_adj_iff_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:46:42.805296+00:00
-- url     : https://prove2.me/submissions/1e6f3a3c-77b8-4bff-8896-4efb8bd8d555

module
public import Definitions.Def_GalvinLib_GaleShapley
public import Definitions.Def_GalvinLib_Kernel
public import Mathlib.Order.Interval.Finset.Fin
public import Definitions.Def_GalvinLib_Orientation
public import Theorems.Thm_Galvin_colour_endA
public import Theorems.Thm_Galvin_colour_endB
public import Theorems.Thm_Galvin_mem_edge_iff

set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace Galvin
theorem _root_.solution (c : G.Coloring (Fin 2)) {e f : G.edgeSet} :
    G.lineGraph.Adj e f ↔ e ≠ f ∧ (endA c e = endA c f ∨ endB c e = endB c f) := by
  rw [lineGraph_adj_iff_exists]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨v, hve, hvf⟩
    rw [mem_edge_iff c] at hve hvf
    have hA := colour_endA c e
    have hA' := colour_endA c f
    have hB := colour_endB c e
    have hB' := colour_endB c f
    rcases hve with rfl | rfl <;> rcases hvf with h | h
    · exact Or.inl h
    · rw [h, hB'] at hA; exact absurd hA (by decide)
    · rw [h, hA'] at hB; exact absurd hB (by decide)
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨endA c e, (mem_edge_iff c e _).2 (Or.inl rfl), (mem_edge_iff c f _).2 (Or.inl h)⟩
    · exact ⟨endB c e, (mem_edge_iff c e _).2 (Or.inr rfl), (mem_edge_iff c f _).2 (Or.inr h)⟩
end Galvin
