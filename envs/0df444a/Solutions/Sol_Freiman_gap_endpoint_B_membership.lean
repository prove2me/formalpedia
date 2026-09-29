-- Prove2me | solution 1 for Freiman.gap_endpoint_B_membership
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:41:18.433389+00:00
-- url     : https://prove2.me/submissions/fe535413-fe61-4214-a734-22cee3719726

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_centered_membership
import Theorems.Thm_Freiman_gap_extremizer_B_global

open Freiman

theorem solution : cF ∈ symbolicMarkovSpectrum := by
  exact gap_centered_membership gapExtremizerB cF gap_extremizer_B_global.1 gap_extremizer_B_global.2
