-- Prove2me | solution 1 for Erdos919.chromaticCardinal_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:13:13.493182+00:00
-- url     : https://prove2.me/submissions/0cb0c72a-0221-4a32-bb60-6216dfe7c65b

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
theorem _root_.solution {V : Type u} (G : SimpleGraph V) (κ : Cardinal.{u}) :
    G.chromaticCardinal ≤ κ ↔ ∃ C : Type u, #C ≤ κ ∧ Nonempty (G.Coloring C) := by
  have hne : Set.Nonempty
      {κ : Cardinal.{u} | ∃ (C : Type u) (_ : #C = κ), Nonempty (G.Coloring C)} :=
    ⟨#V, show ∃ (C : Type u) (_ : #C = #V), Nonempty (G.Coloring C) from
      ⟨V, rfl, ⟨G.selfColoring⟩⟩⟩
  unfold SimpleGraph.chromaticCardinal
  constructor
  · intro h
    obtain ⟨C, hC, hc⟩ := csInf_mem hne
    exact ⟨C, hC.trans_le h, hc⟩
  · rintro ⟨C, hC, hc⟩
    refine le_trans (csInf_le' ?_) hC
    exact ⟨C, rfl, hc⟩
end Erdos919
