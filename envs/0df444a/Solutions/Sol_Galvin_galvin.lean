-- Prove2me | solution 1 for Galvin.galvin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:19:26.101293+00:00
-- url     : https://prove2.me/submissions/fe3281ff-8cb5-4254-b465-4157670fe364

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Definitions.Def_Konig_Basic
public import Definitions.Def_GalvinLib_Orientation
public import Definitions.Def_GalvinLib_Galvin
public import Theorems.Thm_Galvin_card_arc_lt
public import Theorems.Thm_Galvin_exists_listColoring
public import Theorems.Thm_Galvin_hasKernels_arc
public import Theorems.Thm_Konig_lineGraph_colorable_of_colorable_two


set_option autoImplicit true
@[expose] public section
public section
open Galvin
namespace Galvin
theorem _root_.solution {V Color : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) (lists : G.edgeSet → Finset Color)
    (hLists : ∀ e, G.maxDegree ≤ (lists e).card) :
    ∃ coloring : G.lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e := by
  classical
  obtain ⟨c⟩ := hG
  obtain ⟨φ⟩ := Konig.lineGraph_colorable_of_colorable_two G ⟨c⟩
  exact exists_listColoring G.lineGraph (arc c φ) (hasKernels_arc c φ) lists
    fun e => lt_of_lt_of_le (card_arc_lt c φ e) (hLists e)
end Galvin
