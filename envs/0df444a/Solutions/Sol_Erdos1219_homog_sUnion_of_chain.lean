-- Prove2me | solution 1 for Erdos1219.homog_sUnion_of_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:36.495792+00:00
-- url     : https://prove2.me/submissions/db01b17d-c79e-4915-baba-8d0c345e0351

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado

set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {W : Type u} [LinearOrder W] [WellFoundedLT W]
omit [LinearOrder W] [WellFoundedLT W]
namespace Erdos1219
theorem _root_.solution {f : W → W → Bool} {c : Bool} {ch : Set (Set W)}
    (hch : IsChain (· ⊆ ·) ch) (hh : ∀ Z ∈ ch, Homog f c Z) : Homog f c (⋃₀ ch) := by
  intro x hx y hy hxy
  obtain ⟨Z₁, hZ₁, hx⟩ := mem_sUnion.1 hx
  obtain ⟨Z₂, hZ₂, hy⟩ := mem_sUnion.1 hy
  rcases hch.total hZ₁ hZ₂ with h | h
  · exact hh Z₂ hZ₂ x (h hx) y hy hxy
  · exact hh Z₁ hZ₁ x hx y (h hy) hxy
end Erdos1219
