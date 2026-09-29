-- Prove2me | solution 1 for Freiman.gap_forcing_coverage_3
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:42:52.965781+00:00
-- url     : https://prove2.me/submissions/e5172e0a-3cfc-46cf-8a78-47f1a6e65ac8

import Definitions.Def_Freiman_gapCertificateData

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

open Freiman

theorem solution : gapCoverage gapForcingTree3 := by
  simp [gapForcingTree3, gapCoverage, gapRoot, gapExtend]

