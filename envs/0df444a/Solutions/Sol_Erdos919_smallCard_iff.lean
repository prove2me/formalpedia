-- Prove2me | solution 1 for Erdos919.smallCard_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:37:25.025882+00:00
-- url     : https://prove2.me/submissions/dcf114f8-b8c2-4c20-b58c-0e54ec47a5bd

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_ColorableOn_mono_set
public import Theorems.Thm_Erdos919_aleph1_lt_aleph2
public import Theorems.Thm_Erdos919_induce_le_aleph0_iff
public import Theorems.Thm_Erdos919_exists_superset_aleph1

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {V : Type u} (hV : #V = ℵ_ 2) (G : SimpleGraph V) :
    SmallCardCC G ↔ ∀ (X : Set V) (_ : #X = ℵ₁), (G.induce X).chromaticCardinal ≤ ℵ₀ := by
  constructor
  · intro h X hX
    exact (induce_le_aleph0_iff G X).2 (h X hX.le)
  · intro h X hX
    obtain ⟨Y, hXY, hY⟩ := exists_superset_aleph1 (by rw [hV]; exact aleph1_lt_aleph2.le) X hX
    exact ((induce_le_aleph0_iff G Y).1 (h Y hY)).mono_set hXY
end Erdos919
