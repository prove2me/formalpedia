-- Prove2me | solution 1 for Erdos919.inc_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:39:48.283752+00:00
-- url     : https://prove2.me/submissions/45b5b977-3465-471a-ac50-a307d9ef28d4

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_aleph0_lt_chromaticCardinal_iff
public import Theorems.Thm_Erdos919_chromaticCardinal_comap_equiv
public import Theorems.Thm_Erdos919_size_iff

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution :
    (∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ ℵ₀ < G.chromaticCardinal ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀) ↔
    ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ IsEmpty (H.Coloring ℕ) := by
  rw [size_iff (fun G => ℵ₀ < G.chromaticCardinal)
    (fun e G => by rw [chromaticCardinal_comap_equiv])]
  refine exists_congr fun H => ?_
  rw [aleph0_lt_chromaticCardinal_iff H]
end Erdos919
