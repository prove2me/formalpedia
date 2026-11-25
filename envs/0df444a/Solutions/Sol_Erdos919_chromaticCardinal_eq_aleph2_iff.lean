-- Prove2me | solution 1 for Erdos919.chromaticCardinal_eq_aleph2_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:36:51.74589+00:00
-- url     : https://prove2.me/submissions/de7fc5e3-3fd7-4416-827f-cde53490145b

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_aleph2_eq_succ
public import Theorems.Thm_Erdos919_aleph1_lt_aleph2
public import Theorems.Thm_Erdos919_chromaticCardinal_le_iff
public import Theorems.Thm_Erdos919_chromaticCardinal_le_mk

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {V : Type u} (G : SimpleGraph V) (hV : #V = ℵ_ 2) :
    G.chromaticCardinal = ℵ_ 2 ↔ ChiAleph2 G := by
  have hle : G.chromaticCardinal ≤ Order.succ ℵ₁ := by
    rw [← aleph2_eq_succ, ← hV]; exact chromaticCardinal_le_mk G
  have key : G.chromaticCardinal ≤ ℵ₁ ↔ ¬ ChiAleph2 G := by
    rw [chromaticCardinal_le_iff]
    simp only [ChiAleph2, not_forall, not_isEmpty_iff, exists_prop]
  constructor
  · intro h
    by_contra hn
    have := key.2 hn
    rw [h] at this
    exact absurd this (not_le.2 aleph1_lt_aleph2)
  · intro h
    rcases Order.le_succ_iff_eq_or_le.1 hle with h1 | h1
    · rw [h1, aleph2_eq_succ]
    · exact absurd h (key.1 h1)
end Erdos919
