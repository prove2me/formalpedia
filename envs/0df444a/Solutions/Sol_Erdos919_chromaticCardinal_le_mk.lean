-- Prove2me | solution 1 for Erdos919.chromaticCardinal_le_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:34:53.728446+00:00
-- url     : https://prove2.me/submissions/e5f72f6e-2ffc-4d50-837f-254c725cc021

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
theorem _root_.solution {V : Type u} (G : SimpleGraph V) : G.chromaticCardinal ≤ #V :=
  (chromaticCardinal_le_iff G _).2 ⟨V, le_rfl, ⟨G.selfColoring⟩⟩
end Erdos919
