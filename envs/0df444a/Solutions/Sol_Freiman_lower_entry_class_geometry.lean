-- Prove2me | solution 1 for Freiman.lower_entry_class_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:35.623912+00:00
-- url     : https://prove2.me/submissions/2d45e37f-557d-4083-9feb-c889ece79b82

import Theorems.Thm_Freiman_lower_entry_child_orientation
import Theorems.Thm_Freiman_lower_entry_virtual_nn
import Theorems.Thm_Freiman_lower_entry_good_rows
import Theorems.Thm_Freiman_lower_entry_core_rows
import Theorems.Thm_Freiman_lower_entry_contact_rows
import Theorems.Thm_Freiman_lower_entry_goodness_threeEven
import Theorems.Thm_Freiman_lower_entry_cores_threeEven
import Theorems.Thm_Freiman_lower_entry_chain_threeEven
import Theorems.Thm_Freiman_lower_entry_goodness_threeOdd
import Theorems.Thm_Freiman_lower_entry_cores_threeOdd
import Theorems.Thm_Freiman_lower_entry_chain_threeOdd
import Theorems.Thm_Freiman_lower_entry_goodness_twoOdd
import Theorems.Thm_Freiman_lower_entry_cores_twoOdd
import Theorems.Thm_Freiman_lower_entry_chain_twoOdd
import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (c : LowerEntryClass) (p : LowerPair) (hc : lowerEntryContext c p) (hd : lowerEntryDomain p) :
    (∀ l ∈ lowerEntryLabels, lowerStrictGood (lowerChild p l)) ∧
    lowerEntryH c p ⊆ {t | ∃ l ∈ lowerEntryLabels, t ∈ lowerCover (lowerChild p l)} := by
  have ho := lower_entry_child_orientation p hd hc.1
  have hv := lower_entry_virtual_nn p hd
  have hg := lower_entry_good_rows c p hc hd
  have he := lower_entry_core_rows c p hc hd
  have ht := lower_entry_contact_rows c p hc hd
  cases c
  · exact ⟨lower_entry_goodness_threeEven p hc hd ho hv hg,
      lower_entry_chain_threeEven p hc ht (lower_entry_cores_threeEven p hc hd ho he)⟩
  · exact ⟨lower_entry_goodness_threeOdd p hc hd ho hv hg,
      lower_entry_chain_threeOdd p hc ht (lower_entry_cores_threeOdd p hc hd ho he)⟩
  · exact ⟨lower_entry_goodness_twoOdd p hc hd ho hv hg,
      lower_entry_chain_twoOdd p hc ht (lower_entry_cores_twoOdd p hc hd ho he)⟩

