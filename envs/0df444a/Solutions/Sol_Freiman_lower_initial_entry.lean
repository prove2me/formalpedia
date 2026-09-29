-- Prove2me | solution 1 for Freiman.lower_initial_entry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:06.562624+00:00
-- url     : https://prove2.me/submissions/93353526-95ac-43f6-a673-e03bdf12e339

import Theorems.Thm_Freiman_lower_initial_cover
import Theorems.Thm_Freiman_lower_explicit_values
import Theorems.Thm_Freiman_lower_fixed_roots_good
import Theorems.Thm_Freiman_lower_family_root
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (ht : t ∈ Set.Icc cF (Real.sqrt 21)) :
    lowerHasValue t ∨ ∃ p : LowerPair, lowerInitialRoot t p ∧ lowerState t p := by
  rcases lower_initial_cover ht with he | hf | hp
  · exact Or.inl (lower_explicit_values t he)
  · rcases hf with ⟨p,hp,htp⟩
    rcases lower_fixed_roots_good p hp with ⟨ha,hg,hb⟩
    exact Or.inr ⟨p,Or.inl hp,ha,hg,htp,hb⟩
  · exact Or.inr (lower_family_root t hp)
