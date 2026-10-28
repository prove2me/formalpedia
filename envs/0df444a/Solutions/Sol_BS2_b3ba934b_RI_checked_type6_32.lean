-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_32
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:41:39.953547+00:00
-- url     : https://prove2.me/submissions/6ae70b47-a378-4647-abc4-311a52c269ef

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_32_assembly_from0
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7]=true := ThreeBoundRecordLookup.checkTypes_of_from ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] BS2_b3ba934b_RI_checked_type6_32_assembly_from0
