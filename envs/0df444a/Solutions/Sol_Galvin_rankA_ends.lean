-- Prove2me | solution 1 for Galvin.rankA_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:38:04.728101+00:00
-- url     : https://prove2.me/submissions/b1047f97-8e56-47ae-8e14-e5e7b594ad7b

module
public import Definitions.Def_GalvinLib_GaleShapley
public import Definitions.Def_GalvinLib_Kernel
public import Mathlib.Order.Interval.Finset.Fin
public import Definitions.Def_GalvinLib_Orientation
public import Theorems.Thm_Galvin_choose_ends_eq

set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace Galvin
theorem _root_.solution (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (idx : V → ℕ) (e : G.edgeSet) : rankA c φ idx (endA c e) (endB c e) = φ e := by
  have h : ∃ f : G.edgeSet, endA c f = endA c e ∧ endB c f = endB c e := ⟨e, rfl, rfl⟩
  rw [rankA]
  split_ifs
  rw [choose_ends_eq c e h]
end Galvin
