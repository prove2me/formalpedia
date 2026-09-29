-- Prove2me | solution 1 for CKLaneA3X.Step026.remainder_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:46:22.754082+00:00
-- url     : https://prove2.me/submissions/737321d5-f219-489f-a997-3f9e1c3cc957

import Theorems.Thm_CKLaneA3X_Step026_entryBounds_D_m
import Theorems.Thm_CKLaneA3X_Step026_entryBounds_D_inner
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (TMd.mul D_m D_inner 2 1 24).r ≤ D_mInner.r := by
  change rup (mulRem (entryBounds D_m.P) (entryBounds D_inner.P)
    D_m.r D_inner.r D_m.n D_inner.n 2 1 24) ≤ D_mInner.r
  rw [CKLaneA3X.Step026.entryBounds_D_m, CKLaneA3X.Step026.entryBounds_D_inner]
  decide +kernel
