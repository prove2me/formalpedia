-- Prove2me | solution 1 for Erdos919.aleph0_lt_chromaticCardinal_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:33:24.860636+00:00
-- url     : https://prove2.me/submissions/778968b3-458f-4a58-8cd1-f507f937f969

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_chromaticCardinal_le_aleph0_iff

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {V : Type u} (G : SimpleGraph V) :
    ℵ₀ < G.chromaticCardinal ↔ IsEmpty (G.Coloring ℕ) := by
  rw [← not_le, chromaticCardinal_le_aleph0_iff, not_nonempty_iff]
end Erdos919
