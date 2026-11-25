-- Prove2me | solution 1 for Erdos919.induce_le_aleph0_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:34:58.109426+00:00
-- url     : https://prove2.me/submissions/d50e1027-8201-4a77-99fa-e0a02438f8e3

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_colorableOn_iff_induce
public import Theorems.Thm_Erdos919_chromaticCardinal_le_aleph0_iff

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {V : Type u} (G : SimpleGraph V) (X : Set V) :
    (G.induce X).chromaticCardinal ≤ ℵ₀ ↔ ColorableOn G X ℕ := by
  rw [chromaticCardinal_le_aleph0_iff, colorableOn_iff_induce]
end Erdos919
