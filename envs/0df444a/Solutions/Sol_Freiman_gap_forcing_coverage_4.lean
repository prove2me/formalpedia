-- Prove2me | solution 1 for Freiman.gap_forcing_coverage_4
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:43:18.33314+00:00
-- url     : https://prove2.me/submissions/06811f3e-e125-42c5-8a8b-8957ddb262b8

import Definitions.Def_Freiman_gapCertificateData

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

open Freiman

theorem solution : gapCoverage gapForcingTree4 := by
  simp [gapForcingTree4, gapCoverage, gapRoot, gapExtend]

