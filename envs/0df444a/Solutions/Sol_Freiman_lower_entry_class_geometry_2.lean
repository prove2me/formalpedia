-- Prove2me | solution 2 for Freiman.lower_entry_class_geometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:18:14.722558+00:00
-- url     : https://prove2.me/submissions/a7daccfd-ee3c-4bf0-be31-da5e3537b1d2

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_initial_word_fraction
import Theorems.Thm_Freiman_lower_initial_matrix_bottom
import Theorems.Thm_Freiman_lower_entry_domain_normalizes
import Theorems.Thm_Freiman_lower_entry_child_orientation
import Theorems.Thm_Freiman_lower_entry_virtual_nn
import Theorems.Thm_Freiman_lower_entry_good_rows
import Theorems.Thm_Freiman_lower_entry_contact_rows
import Theorems.Thm_Freiman_lower_entry_core_rows
import Theorems.Thm_Freiman_lower_entry_cores_threeEven
import Theorems.Thm_Freiman_lower_entry_cores_threeOdd
import Theorems.Thm_Freiman_lower_entry_cores_twoOdd
import Theorems.Thm_Freiman_lower_entry_chain_threeEven
import Theorems.Thm_Freiman_lower_entry_chain_threeOdd
import Theorems.Thm_Freiman_lower_entry_chain_twoOdd
import Theorems.Thm_Freiman_lower_entry_goodness_threeEven
import Theorems.Thm_Freiman_lower_entry_goodness_threeOdd
import Theorems.Thm_Freiman_lower_entry_goodness_twoOdd

open Freiman

-- The class geometry packages strict goodness of every entry child together with the
-- coverage of the class interval by those children. Both halves are already factored:
-- orientation / virtual-NN / rows feed the goodness nodes, and rows / orientation /
-- cores feed the chain nodes. The normalisation hypothesis needed by the orientation
-- lemma comes from `lower_entry_domain_normalizes`, whose two side inputs are exactly
-- `lower_initial_word_fraction` and `lower_initial_matrix_bottom`.
theorem solution (c : LowerEntryClass) (p : LowerPair) (hc : lowerEntryContext c p)
    (hd : lowerEntryDomain p) :
    (∀ l ∈ lowerEntryLabels, lowerStrictGood (lowerChild p l)) ∧
    lowerEntryH c p ⊆ {t | ∃ l ∈ lowerEntryLabels, t ∈ lowerCover (lowerChild p l)} := by
  have hn : lowerNormalize p = p :=
    lower_entry_domain_normalizes (fun w t ht => lower_initial_word_fraction w t ht)
      lower_initial_matrix_bottom p hd
  have ho : lowerEntryChildOrientation p := lower_entry_child_orientation p hd hn
  have hv : lowerEntryVirtualNN p := lower_entry_virtual_nn p hd
  cases c with
  | threeEven =>
      exact ⟨lower_entry_goodness_threeEven p hc hd ho hv
          (lower_entry_good_rows .threeEven p hc hd),
        lower_entry_chain_threeEven p hc (lower_entry_contact_rows .threeEven p hc hd)
          (lower_entry_cores_threeEven p hc hd ho (lower_entry_core_rows .threeEven p hc hd))⟩
  | threeOdd =>
      exact ⟨lower_entry_goodness_threeOdd p hc hd ho hv
          (lower_entry_good_rows .threeOdd p hc hd),
        lower_entry_chain_threeOdd p hc (lower_entry_contact_rows .threeOdd p hc hd)
          (lower_entry_cores_threeOdd p hc hd ho (lower_entry_core_rows .threeOdd p hc hd))⟩
  | twoOdd =>
      exact ⟨lower_entry_goodness_twoOdd p hc hd ho hv
          (lower_entry_good_rows .twoOdd p hc hd),
        lower_entry_chain_twoOdd p hc (lower_entry_contact_rows .twoOdd p hc hd)
          (lower_entry_cores_twoOdd p hc hd ho (lower_entry_core_rows .twoOdd p hc hd))⟩
