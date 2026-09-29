-- Prove2me | solution 1 for CKLaneA3X.Step026.input_conditions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:53:05.51446+00:00
-- url     : https://prove2.me/submissions/11bf1d74-277d-426a-b17f-a3be1c613160

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (zeroPrefix D_m.P 2 = true) ∧ (zeroPrefix D_inner.P 1 = true) ∧ (2 ≤ D_m.n) ∧ (24 ≤ 2 + D_inner.n) ∧ (24 ≤ 1 + D_m.n) := by
  decide +kernel
