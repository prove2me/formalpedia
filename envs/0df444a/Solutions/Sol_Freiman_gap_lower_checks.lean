-- Prove2me | solution 1 for Freiman.gap_lower_checks
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:38:18.520165+00:00
-- url     : https://prove2.me/submissions/a07a695d-67a7-4545-93cc-ea6b81e6b4fb

import Definitions.Def_Freiman_gapCertificateData
import Theorems.Thm_Freiman_gap_lower_checks_2_6
import Theorems.Thm_Freiman_gap_lower_checks_7_11
import Theorems.Thm_Freiman_gap_lower_checks_12_16
import Theorems.Thm_Freiman_gap_lower_checks_17_20

open Freiman

theorem solution : ∀ n : ℕ, n < 19 → gapChecks (gapLowerRows.take n) [] .forbidden (gapLowerTrees[n]!) := by
  intro n hn
  by_cases h5 : n < 5
  · exact gap_lower_checks_2_6 n (Nat.zero_le n) h5
  by_cases h10 : n < 10
  · exact gap_lower_checks_7_11 n (by omega) h10
  by_cases h15 : n < 15
  · exact gap_lower_checks_12_16 n (by omega) h15
  · exact gap_lower_checks_17_20 n (by omega) hn
