-- Prove2me | solution 1 for Freiman.gap_upper_checks
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:38:30.109974+00:00
-- url     : https://prove2.me/submissions/cdef5cc4-77ec-4009-bf5c-534484be30ff

import Definitions.Def_Freiman_gapCertificateData
import Theorems.Thm_Freiman_gap_upper_checks_21_24
import Theorems.Thm_Freiman_gap_upper_checks_25_28
import Theorems.Thm_Freiman_gap_upper_checks_29_31

open Freiman

theorem solution : ∀ n : ℕ, n < 11 → gapChecks [] [] (.upper (gapUpperRows[n]!).bound) (gapUpperTrees[n]!) := by
  intro n hn
  by_cases h4 : n < 4
  · exact gap_upper_checks_21_24 n (Nat.zero_le n) h4
  by_cases h8 : n < 8
  · exact gap_upper_checks_25_28 n (by omega) h8
  · exact gap_upper_checks_29_31 n (by omega) hn
