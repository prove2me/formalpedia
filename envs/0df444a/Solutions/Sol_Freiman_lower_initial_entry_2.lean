-- Prove2me | solution 2 for Freiman.lower_initial_entry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T21:57:18.682303+00:00
-- url     : https://prove2.me/submissions/1afafdb0-3f6c-4a0b-a86a-f1e6a09fbe21

import Definitions.Def_Freiman_lowerCertificates
import Theorems.Thm_Freiman_lower_initial_cover
import Theorems.Thm_Freiman_lower_explicit_values
import Theorems.Thm_Freiman_lower_fixed_roots_good
import Theorems.Thm_Freiman_lower_family_root

open Freiman

theorem solution (t : ℝ) (ht : t ∈ Set.Icc cF (Real.sqrt 21)) :
    lowerHasValue t ∨ ∃ p : LowerPair, lowerInitialRoot t p ∧ lowerState t p := by
  rcases lower_initial_cover ⟨ht.1, ht.2⟩ with hexp | hfixed | hfamily
  · exact Or.inl (lower_explicit_values t hexp)
  · rcases hfixed with ⟨p, hp, hcover⟩
    have hgood := lower_fixed_roots_good p hp
    exact Or.inr ⟨p, Or.inl hp, ⟨hgood.1, hgood.2.1, hcover, hgood.2.2⟩⟩
  · exact Or.inr (lower_family_root t hfamily)
