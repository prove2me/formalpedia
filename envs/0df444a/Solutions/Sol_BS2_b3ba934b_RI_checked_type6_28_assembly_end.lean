-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_28_assembly_end
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:45:53.240795+00:00
-- url     : https://prove2.me/submissions/bb2fb647-8fc8-4c33-b2ba-8b9d146c84a5

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 424=true := ThreeBoundRecordLookup.checkCasesFrom_end ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 424 (by decide +kernel)
