-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_31_assembly_end
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:34:17.625479+00:00
-- url     : https://prove2.me/submissions/ae4e0d7e-6ad8-4a67-bd00-ec60d1b3be85

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 688=true := ThreeBoundRecordLookup.checkCasesFrom_end ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 688 (by decide +kernel)
