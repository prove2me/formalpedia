-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_length7_coverage_tail000
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:48:13.249914+00:00
-- url     : https://prove2.me/submissions/80148bb3-a5f8-4626-8660-5db1bf1dcb7c

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Theorems.Thm_BS2_b3ba934b_RI_checked_type7_0
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (([[5,5,5,5,5,5,5]] : List (List ThreeBoundQ2.Kind)).all (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree))=true := by
  exact ThreeBoundRecordLookup.all_cons_of _ _ _ BS2_b3ba934b_RI_checked_type7_0 (rfl)
