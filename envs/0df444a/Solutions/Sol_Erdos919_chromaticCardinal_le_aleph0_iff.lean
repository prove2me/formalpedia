-- Prove2me | solution 1 for Erdos919.chromaticCardinal_le_aleph0_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:32:34.960696+00:00
-- url     : https://prove2.me/submissions/03d2a8cb-89b4-4ffc-bfeb-707ba650d758

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
theorem _root_.solution {V : Type u} (G : SimpleGraph V) :
    G.chromaticCardinal ≤ ℵ₀ ↔ Nonempty (G.Coloring ℕ) := by
  rw [chromaticCardinal_le_iff]
  constructor
  · rintro ⟨C, hC, ⟨c⟩⟩
    have : Countable C := mk_le_aleph0_iff.1 hC
    obtain ⟨f, hf⟩ := (countable_iff_exists_injective C).1 this
    exact ⟨Coloring.mk (f ∘ c) (fun h e => c.valid h (hf e))⟩
  · rintro ⟨c⟩
    exact ⟨ULift ℕ, by rw [mk_uLift, mk_nat, lift_aleph0], ⟨coloringULift c⟩⟩
end Erdos919
