-- Prove2me | solution 1 for Freiman.gap_leaf_terminal_soundness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:44:20.355623+00:00
-- url     : https://prove2.me/submissions/1c641951-a2fb-4f4b-a3a7-45685fffaea4

import Definitions.Def_Freiman_gapCertificate
import Theorems.Thm_Freiman_gap_match_alignment

open Freiman

theorem solution (lower upper : List GapRow) (mode : GapMode) (s : GapState) (a : ℤ → ℕ+) (i : ℤ) (hd : gapDigits a) (hc : gapCapped a) (hl : gapLowerValid a lower) (hu : gapUpperValid a upper) (hm : gapMatch a i s) (hcheck : gapLeafCheck lower upper mode s .terminal) : gapModeOutcome mode a i := by
  rcases hcheck with ⟨rfl,h⟩
  change gapWindow < localValue a i → gapReduced a i
  intro _
  rcases h with h | h | h | h
  · exact Or.inl (gap_match_alignment a i s gapSeedA hm (by decide) h)
  · exact Or.inr (Or.inl (gap_match_alignment a i s (gapReverse gapSeedA) hm (by decide) h))
  · exact Or.inr (Or.inr (Or.inl (gap_match_alignment a i s gapSeedB hm (by decide) h)))
  · exact Or.inr (Or.inr (Or.inr (gap_match_alignment a i s (gapReverse gapSeedB) hm (by decide) h)))
