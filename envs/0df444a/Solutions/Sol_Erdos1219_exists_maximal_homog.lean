-- Prove2me | solution 1 for Erdos1219.exists_maximal_homog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:45:45.076831+00:00
-- url     : https://prove2.me/submissions/edee5f2d-af29-4493-b217-dd089ae343be

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Theorems.Thm_Erdos1219_homog_sUnion_of_chain
import Theorems.Thm_Erdos1219_Homog_empty


set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {W : Type u} [LinearOrder W] [WellFoundedLT W]
omit [LinearOrder W] [WellFoundedLT W]
namespace Erdos1219
theorem _root_.solution (f : W → W → Bool) (c : Bool) (A : Set W) :
    ∃ Z, Maximal (· ∈ {Z : Set W | Z ⊆ A ∧ Homog f c Z}) Z := by
  have hchain : ∀ ch ⊆ {Z : Set W | Z ⊆ A ∧ Homog f c Z}, IsChain (· ⊆ ·) ch → ch.Nonempty →
      ∃ ub ∈ {Z : Set W | Z ⊆ A ∧ Homog f c Z}, ∀ s ∈ ch, s ⊆ ub := by
    intro ch hch hchain _
    exact ⟨⋃₀ ch, ⟨sUnion_subset fun Z hZ => (hch hZ).1,
      homog_sUnion_of_chain hchain fun Z hZ => (hch hZ).2⟩, fun Z hZ => subset_sUnion_of_mem hZ⟩
  obtain ⟨Z, -, hZ⟩ := zorn_subset_nonempty {Z : Set W | Z ⊆ A ∧ Homog f c Z} hchain ∅
    ⟨empty_subset _, Homog.empty f c⟩
  exact ⟨Z, hZ⟩
end Erdos1219
