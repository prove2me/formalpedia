-- Prove2me | solution 1 for ErdosGirth.exists_girth_chromaticNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:39:50.703082+00:00
-- url     : https://prove2.me/submissions/861661eb-9d37-4bab-82e2-30ea0a644160

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
public import Definitions.Def_GirthLib_ErdosGirth
public import Theorems.Thm_ErdosGirth_exists_girth_not_colorable

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution (g k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), (g : ℕ∞) < G.egirth ∧ (k : ℕ∞) < G.chromaticNumber := by
  obtain ⟨N, hN⟩ := exists_girth_not_colorable g k
  obtain ⟨G, hG, hc⟩ := hN N le_rfl
  exact ⟨N, G, hG, lt_of_not_ge fun h => hc (chromaticNumber_le_iff_colorable.mp h)⟩
end ErdosGirth
