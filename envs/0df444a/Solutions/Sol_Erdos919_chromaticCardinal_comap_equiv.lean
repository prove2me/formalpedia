-- Prove2me | solution 1 for Erdos919.chromaticCardinal_comap_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:24:07.506592+00:00
-- url     : https://prove2.me/submissions/8df8ce22-4ade-44ed-ab91-042db6d8ade7

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_chromaticCardinal_le_iff

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {A B : Type u} (e : A ≃ B) (G : SimpleGraph B) :
    (G.comap e).chromaticCardinal = G.chromaticCardinal := by
  have h : ∀ κ, (G.comap e).chromaticCardinal ≤ κ ↔ G.chromaticCardinal ≤ κ := fun κ => by
    rw [chromaticCardinal_le_iff, chromaticCardinal_le_iff]
    exact ⟨fun ⟨C, hC, ⟨c⟩⟩ => ⟨C, hC, ⟨coloringOfComap e c⟩⟩,
      fun ⟨C, hC, ⟨c⟩⟩ => ⟨C, hC, ⟨coloringComap e c⟩⟩⟩
  exact le_antisymm ((h _).2 le_rfl) ((h _).1 le_rfl)
end Erdos919
