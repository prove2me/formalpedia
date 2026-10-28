-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_27_chunk4672
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:40:30.070972+00:00
-- url     : https://prove2.me/submissions/7ccabf02-b505-494b-bb52-5aee6f6906a4

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4672 64=true := by decide +kernel
