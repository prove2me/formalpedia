-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_30_chunk64
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:34:06.132827+00:00
-- url     : https://prove2.me/submissions/992688d1-fd58-46b4-99be-af51ef6593f0

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,6,7] 64 16=true := by decide +kernel
