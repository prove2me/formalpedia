-- Prove2me | solution 1 for Freiman.lower_one_step
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:40.633026+00:00
-- url     : https://prove2.me/submissions/4b937f41-0737-47f9-b184-f4ac298771be

import Theorems.Thm_Freiman_lower_geometry_cover
import Theorems.Thm_Freiman_lower_suffix_targets
import Theorems.Thm_Freiman_lower_p97_target
import Theorems.Thm_Freiman_lower_late_entry_domain
import Theorems.Thm_Freiman_lower_priority_choice
import Theorems.Thm_Freiman_lower_selected_words
import Theorems.Thm_Freiman_lower_parameter_extension
import Theorems.Thm_Freiman_lower_parameter_normalize
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) :
    lowerHasValue t ∨ ∃ l : LowerLabel, lowerOffered (h n) l ∧ lowerPriority t (h n) l ∧
      lowerState t (lowerChild (h n) l) := by
  have hs := hh.2.1 n (le_refl n)
  rcases lower_geometry_cover t (h n) hs (lower_suffix_targets t h n hh)
    (lower_p97_target t h n hh) (lower_late_entry_domain t h n hh) with he | hc
  · exact Or.inl he
  · rcases lower_priority_choice t h n hh hc with ⟨l,hl,hp,hg,ht⟩
    rcases lower_selected_words t h n hh l hl with ⟨ha,he,_⟩
    exact Or.inr ⟨l,hl,hp,ha,hg,ht,lower_parameter_extension _ _ (lower_parameter_normalize _ hs.2.2.2) he⟩
