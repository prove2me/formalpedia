-- Prove2me | solution 1 for Galvin.gale_shapley
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:34:55.905624+00:00
-- url     : https://prove2.me/submissions/9f93de24-14e2-4374-932f-6a89634320d2

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Definitions.Def_Konig_Basic
public import Definitions.Def_GalvinLib_Orientation
public import Definitions.Def_GalvinLib_Galvin
public import Theorems.Thm_Galvin_exists_isStable


set_option autoImplicit true
@[expose] public section
public section
open Galvin
namespace Galvin
theorem _root_.solution {M W : Type*} [Finite M] [Finite W] (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) :
    ∃ μ : M → W → Prop, (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m) := by
  exact exists_isStable rm rw hrm hrw _ E rfl
end Galvin
