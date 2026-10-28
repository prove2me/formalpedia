-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_30_assembly_end
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:34:01.476994+00:00
-- url     : https://prove2.me/submissions/3c54ae79-35f4-4e69-9463-0e003b3f7a2e

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,6,7] 80=true := ThreeBoundRecordLookup.checkCasesFrom_end ThreeBoundEndpoint40Records.tree [5,5,5,5,6,7] 80 (by decide +kernel)
