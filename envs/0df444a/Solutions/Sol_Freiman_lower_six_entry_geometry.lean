-- Prove2me | solution 1 for Freiman.lower_six_entry_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:35.82907+00:00
-- url     : https://prove2.me/submissions/abcf66b5-554b-4041-a3f8-4eb2ff2dcd3f

import Theorems.Thm_Freiman_lower_entry_family_context
import Theorems.Thm_Freiman_lower_entry_family_domain
import Theorems.Thm_Freiman_lower_entry_class_geometry
import Theorems.Thm_Freiman_lower_entry_admissible
import Theorems.Thm_Freiman_lower_child_normalize
import Theorems.Thm_Freiman_lower_strict_good_implies_good
import Theorems.Thm_Freiman_lower_entry_child_parameter
import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution : ∀ (f : LowerInitialFamily) (n k p : ℕ),
    (∀ l ∈ lowerEntryLabels, lowerAdmissible (lowerChild (lowerFamilyPair f n k p) l) ∧
      lowerGood (lowerChild (lowerFamilyPair f n k p) l) ∧ lowerParameterBox (lowerChild (lowerFamilyPair f n k p) l)) ∧
    lowerFamilyH f n k p ⊆ {t | ∃ l ∈ lowerEntryLabels, t ∈ lowerCover (lowerChild (lowerFamilyPair f n k p) l)} := by
  intro f n k p
  rcases lower_entry_family_context f n k p with ⟨c,hc,hH⟩
  have hd := lower_entry_family_domain f n k p
  have hg := lower_entry_class_geometry c _ hc hd
  constructor
  · intro l hl
    refine ⟨lower_entry_admissible f n k p l hl,?_,?_⟩
    · simpa only [lower_child_normalize] using lower_strict_good_implies_good _ (hg.1 l hl)
    · simpa only [lower_child_normalize] using lower_entry_child_parameter _ hd hc.1 l hl
  · rw [hH]
    simpa only [lower_child_normalize] using hg.2
