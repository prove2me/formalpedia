-- Prove2me | solution 1 for Freiman.late_checks_transfer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:07:45.813594+00:00
-- url     : https://prove2.me/submissions/bf921218-9fef-48fe-a410-2e8ee918c60c

import Theorems.Thm_Freiman_late_checks_from_endpoint_comparison
import Theorems.Thm_Freiman_late_endpoint_semantics
import Theorems.Thm_Freiman_late_greater_semantics
import Theorems.Thm_Freiman_cert_field_lower_bound
import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem solution : lateChecksLaw := by
  exact late_checks_from_endpoint_comparison late_endpoint_semantics late_greater_semantics cert_field_lower_bound
