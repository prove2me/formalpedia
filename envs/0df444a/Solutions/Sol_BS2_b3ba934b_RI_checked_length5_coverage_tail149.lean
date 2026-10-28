-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_length5_coverage_tail149
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:39:42.372986+00:00
-- url     : https://prove2.me/submissions/0c5f84c0-66a6-440d-867d-772ab6bfcdf7

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Theorems.Thm_BS2_b3ba934b_RI_Batch_618c58463e44
import Theorems.Thm_BS2_b3ba934b_RI_Batch_83689d4e5d10
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (([[5,5,7,7,7],[5,6,7,7,7],[5,7,7,7,7],[7,7,7,7,7]] : List (List ThreeBoundQ2.Kind)).all (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree))=true := by
  exact ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_83689d4e5d10.2.2.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_618c58463e44.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_83689d4e5d10.2.2.2.2.2.2.1) (ThreeBoundRecordLookup.all_cons_of _ _ _ (BS2_b3ba934b_RI_Batch_618c58463e44.2.2.2.1) (rfl))))
