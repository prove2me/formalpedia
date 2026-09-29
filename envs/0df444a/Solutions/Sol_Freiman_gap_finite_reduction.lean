-- Prove2me | solution 1 for Freiman.gap_finite_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:38:29.929814+00:00
-- url     : https://prove2.me/submissions/b9591b93-d7cf-4881-b62d-f833d645efb2

import Definitions.Def_Freiman_gapCertificateData
import Theorems.Thm_Freiman_gap_forcing_application
import Theorems.Thm_Freiman_gap_certificate_soundness
import Theorems.Thm_Freiman_gap_forcing_coverage_3
import Theorems.Thm_Freiman_gap_forcing_coverage_4
import Theorems.Thm_Freiman_gap_forcing_checks_3
import Theorems.Thm_Freiman_gap_forcing_checks_4
import Theorems.Thm_Freiman_gap_lower_table
import Theorems.Thm_Freiman_gap_upper_table

open Freiman

theorem solution (a : ℤ → ℕ+) (hc : gapCapped a) (hw : gapWindow < localValue a 0) : gapReduced a 0 := by
  exact gap_forcing_application gap_certificate_soundness gap_forcing_coverage_3 gap_forcing_coverage_4 gap_forcing_checks_3 gap_forcing_checks_4 a hc (gap_lower_table a hc) (gap_upper_table a hc) hw
