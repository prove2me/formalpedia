-- Prove2me | solution 1 for Erdos919.chromaticCardinal_eq_aleph1_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:35:22.163364+00:00
-- url     : https://prove2.me/submissions/782e85da-eefc-4699-b4e6-1993575d565d

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_chromaticCardinal_le_iff
public import Theorems.Thm_Erdos919_aleph0_lt_chromaticCardinal_iff

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {V : Type u} (G : SimpleGraph V) :
    G.chromaticCardinal = ℵ₁ ↔ ChiAleph1 G := by
  unfold ChiAleph1
  rw [← chromaticCardinal_le_iff, ← aleph0_lt_chromaticCardinal_iff]
  constructor
  · intro h
    rw [h]
    exact ⟨le_rfl, aleph0_lt_aleph_one⟩
  · rintro ⟨h1, h2⟩
    apply le_antisymm h1
    rw [← succ_aleph0]
    exact Order.succ_le_of_lt h2
end Erdos919
