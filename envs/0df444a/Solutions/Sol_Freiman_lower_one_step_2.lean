-- Prove2me | solution 2 for Freiman.lower_one_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T22:06:01.896752+00:00
-- url     : https://prove2.me/submissions/80fb621c-d604-49ca-84b3-f5c88489a13b

import Definitions.Def_Freiman_lowerCertificates
import Theorems.Thm_Freiman_lower_geometry_cover
import Theorems.Thm_Freiman_lower_suffix_targets
import Theorems.Thm_Freiman_lower_p97_target
import Theorems.Thm_Freiman_lower_late_entry_domain
import Theorems.Thm_Freiman_lower_priority_choice
import Theorems.Thm_Freiman_lower_selected_words
import Theorems.Thm_Freiman_lower_parameter_extension
import Theorems.Thm_Freiman_lower_parameter_normalize

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ)
    (hh : lowerHistory t h n) :
    lowerHasValue t ∨ ∃ l : LowerLabel, lowerOffered (h n) l ∧
      lowerPriority t (h n) l ∧ lowerState t (lowerChild (h n) l) := by
  have hs : lowerState t (h n) := hh.2.1 n (le_refl n)
  have hb := lower_suffix_targets t h n hh
  have hp97 := lower_p97_target t h n hh
  have hlate := lower_late_entry_domain t h n hh
  rcases lower_geometry_cover t (h n) hs hb hp97 hlate with hvalue | hgood
  · exact Or.inl hvalue
  rcases lower_priority_choice t h n hh hgood with ⟨l, hlo, hprio, hchildgood, htcover⟩
  have hsel := lower_selected_words t h n hh l hlo
  have hparentbox : lowerParameterBox (h n) := hs.2.2.2
  have hnormbox := lower_parameter_normalize (h n) hparentbox
  have hchildbox := lower_parameter_extension (lowerNormalize (h n))
    (lowerChild (h n) l) hnormbox hsel.2.1
  exact Or.inr ⟨l, hlo, hprio, ⟨hsel.1, hchildgood, htcover, hchildbox⟩⟩
