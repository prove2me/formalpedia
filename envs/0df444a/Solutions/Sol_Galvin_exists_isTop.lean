-- Prove2me | solution 1 for Galvin.exists_isTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:25:32.036912+00:00
-- url     : https://prove2.me/submissions/f7ddecbf-4c81-4d66-b3a1-01651f22aaa6

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Mathlib.Data.Set.Card
public import Definitions.Def_GalvinLib_GaleShapley

set_option autoImplicit true
@[expose] public section
public section
open Galvin
namespace Galvin
theorem _root_.solution {M W : Type*} (E : M → W → Prop) (rm : M → W → ℕ) (m : M) (w : W)
    (h : E m w) : ∃ w', IsTop E rm m w' := by
  classical
  have hex : ∃ k, ∃ w, E m w ∧ rm m w = k := ⟨_, w, h, rfl⟩
  obtain ⟨w', hw', hk⟩ := Nat.find_spec hex
  refine ⟨w', hw', fun v hv => ?_⟩
  rw [hk]
  exact Nat.find_min' hex ⟨v, hv, rfl⟩
end Galvin
