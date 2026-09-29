-- Prove2me | solution 1 for Freiman.gap_upper_table
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:38:30.133058+00:00
-- url     : https://prove2.me/submissions/7b66345e-d279-4547-88d1-fe5a38ca0069

import Definitions.Def_Freiman_gapCertificateData
import Theorems.Thm_Freiman_gap_upper_application
import Theorems.Thm_Freiman_gap_certificate_soundness
import Theorems.Thm_Freiman_gap_upper_binding
import Theorems.Thm_Freiman_gap_upper_coverage
import Theorems.Thm_Freiman_gap_upper_checks
import Theorems.Thm_Freiman_gap_capped_digits

open Freiman

theorem solution (a : ℤ → ℕ+) (hc : gapCapped a) : gapUpperValid a gapUpperRows := by
  exact gap_upper_application gap_certificate_soundness gap_upper_binding gap_upper_coverage gap_upper_checks a (gap_capped_digits a hc) hc
