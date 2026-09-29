-- Prove2me | solution 1 for CKLaneA3X.Step027.remainder_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T03:06:53.516626+00:00
-- url     : https://prove2.me/submissions/ee2e51f9-20c8-4891-b8e2-a49c43ba4bdf

import Theorems.Thm_CKLaneA3X_Step027_entryBounds_D_Us
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution : (TMd.mul D_Us D_Us 1 1 24).r ≤ D_UsUs.r := by
  change rup (mulRem (entryBounds D_Us.P) (entryBounds D_Us.P)
    D_Us.r D_Us.r D_Us.n D_Us.n 1 1 24) ≤ D_UsUs.r
  simp only [CKLaneA3X.Step027.entryBounds_D_Us]
  decide +kernel
