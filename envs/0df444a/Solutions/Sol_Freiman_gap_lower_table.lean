-- Prove2me | solution 1 for Freiman.gap_lower_table
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:38:29.922418+00:00
-- url     : https://prove2.me/submissions/9e55cc46-0357-41ef-a1e6-dffac0a6e745

import Definitions.Def_Freiman_gapCertificateData
import Theorems.Thm_Freiman_gap_lower_application
import Theorems.Thm_Freiman_gap_certificate_soundness
import Theorems.Thm_Freiman_gap_lower_binding
import Theorems.Thm_Freiman_gap_lower_coverage
import Theorems.Thm_Freiman_gap_lower_checks
import Theorems.Thm_Freiman_gap_capped_digits

open Freiman

theorem solution (a : ℤ → ℕ+) (hc : gapCapped a) : gapLowerValid a gapLowerRows := by
  exact gap_lower_application gap_certificate_soundness gap_lower_binding gap_lower_coverage gap_lower_checks a (gap_capped_digits a hc) hc
