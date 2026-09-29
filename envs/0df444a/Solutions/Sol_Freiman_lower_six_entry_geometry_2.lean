-- Prove2me | solution 2 for Freiman.lower_six_entry_geometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:19:07.726353+00:00
-- url     : https://prove2.me/submissions/99a4a820-c6e0-44cb-ba06-a29e0e56295b

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_initial_word_fraction
import Theorems.Thm_Freiman_lower_initial_matrix_bottom
import Theorems.Thm_Freiman_lower_entry_domain_normalizes
import Theorems.Thm_Freiman_lower_entry_child_parameter
import Theorems.Thm_Freiman_lower_entry_admissible
import Theorems.Thm_Freiman_lower_strict_good_implies_good
import Theorems.Thm_Freiman_lower_child_normalize
import Theorems.Thm_Freiman_lower_entry_family_context
import Theorems.Thm_Freiman_lower_entry_family_domain
import Theorems.Thm_Freiman_lower_entry_class_geometry

open Freiman

-- The six ordinary entry covers for an arbitrary initial family pair. Each component is
-- an existing node: admissibility is `lower_entry_admissible`; goodness is the strict
-- goodness from `lower_entry_class_geometry` pushed through
-- `lower_strict_good_implies_good`; the parameter box is `lower_entry_child_parameter`
-- (whose normalisation hypothesis comes from `lower_entry_domain_normalizes`); and the
-- coverage is the second half of `lower_entry_class_geometry`, after rewriting the family
-- interval to the entry-class interval via `lower_entry_family_context`. The passage
-- between `lowerChild` of the family pair and of its normalisation is
-- `lower_child_normalize`.
theorem solution : ∀ (f : LowerInitialFamily) (n k p : ℕ),
    (∀ l ∈ lowerEntryLabels, lowerAdmissible (lowerChild (lowerFamilyPair f n k p) l) ∧
      lowerGood (lowerChild (lowerFamilyPair f n k p) l) ∧
      lowerParameterBox (lowerChild (lowerFamilyPair f n k p) l)) ∧
    lowerFamilyH f n k p ⊆
      {t | ∃ l ∈ lowerEntryLabels, t ∈ lowerCover (lowerChild (lowerFamilyPair f n k p) l)} := by
  intro f n k p
  obtain ⟨c, hctx, hH⟩ := lower_entry_family_context f n k p
  have hdom : lowerEntryDomain (lowerNormalize (lowerFamilyPair f n k p)) :=
    lower_entry_family_domain f n k p
  have hn : lowerNormalize (lowerNormalize (lowerFamilyPair f n k p)) =
      lowerNormalize (lowerFamilyPair f n k p) :=
    lower_entry_domain_normalizes (fun w t ht => lower_initial_word_fraction w t ht)
      lower_initial_matrix_bottom _ hdom
  obtain ⟨hstrict, hcov⟩ :=
    lower_entry_class_geometry c (lowerNormalize (lowerFamilyPair f n k p)) hctx hdom
  refine ⟨?_, ?_⟩
  · intro l hl
    have hs : lowerStrictGood (lowerChild (lowerFamilyPair f n k p) l) := by
      simpa only [lower_child_normalize] using hstrict l hl
    have hbox : lowerParameterBox (lowerChild (lowerFamilyPair f n k p) l) := by
      simpa only [lower_child_normalize] using
        lower_entry_child_parameter (lowerNormalize (lowerFamilyPair f n k p)) hdom hn l hl
    exact ⟨lower_entry_admissible f n k p l hl,
      lower_strict_good_implies_good (lowerChild (lowerFamilyPair f n k p) l) hs, hbox⟩
  · rw [hH]
    intro t ht
    obtain ⟨l, hl, hlt⟩ := hcov ht
    exact ⟨l, hl, by simpa only [lower_child_normalize] using hlt⟩
