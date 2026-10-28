-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type7_0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:46:12.611984+00:00
-- url     : https://prove2.me/submissions/41cc51f4-9003-4e61-99c8-ac0a32fc27e9

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RegularRecord
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5,5]=true := ThreeBoundEndpoint40Regular.checked_type7_regular
