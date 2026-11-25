-- Prove2me | solution 1 for Galvin.isStable_of_removal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:25:47.71728+00:00
-- url     : https://prove2.me/submissions/8f974582-a783-4284-a782-0bee98c68ee0

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
theorem _root_.solution {M W : Type*} (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ)
    {m₁ m₂ : M} {w : W} (h₁ : IsTop E rm m₁ w) (hlt : rw w m₁ < rw w m₂)
    (μ : M → W → Prop)
    (hμ : IsStable (fun m v => E m v ∧ ¬ (m = m₂ ∧ v = w)) rm rw μ) (hne : m₁ ≠ m₂) :
    IsStable E rm rw μ := by
  obtain ⟨hsub, hm, hw, hst⟩ := hμ
  refine ⟨fun m v h => (hsub m v h).1, hm, hw, fun m v hE hnot => ?_⟩
  by_cases hrem : m = m₂ ∧ v = w
  · obtain ⟨rfl, rfl⟩ := hrem
    right
    by_cases hμ₁ : μ m₁ v
    · exact ⟨m₁, hμ₁, hlt⟩
    · rcases hst m₁ v ⟨h₁.1, fun h => hne h.1⟩ hμ₁ with ⟨w', hw', hr⟩ | ⟨m', hm', hr⟩
      · exact absurd (h₁.2 w' (hsub _ _ hw').1) (not_le.mpr hr)
      · exact ⟨m', hm', hr.trans hlt⟩
  · exact hst m v ⟨hE, hrem⟩ hnot
end Galvin
