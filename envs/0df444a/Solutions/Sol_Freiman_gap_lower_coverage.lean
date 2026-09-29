-- Prove2me | solution 1 for Freiman.gap_lower_coverage
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:43:41.381641+00:00
-- url     : https://prove2.me/submissions/b90779cd-ddf2-452b-aa31-8bb2c0d59910

import Definitions.Def_Freiman_gapCertificateData

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

open Freiman

theorem solution : ∀ tree ∈ gapLowerTrees, gapCoverage tree := by
  simp [gapLowerTrees, gapLowerTree2, gapLowerTree3, gapLowerTree4, gapLowerTree5, gapLowerTree6, gapLowerTree7, gapLowerTree8, gapLowerTree9, gapLowerTree10, gapLowerTree11, gapLowerTree12, gapLowerTree13, gapLowerTree14, gapLowerTree15, gapLowerTree16, gapLowerTree17, gapLowerTree18, gapLowerTree19, gapLowerTree20, gapCoverage, gapRoot, gapExtend]

