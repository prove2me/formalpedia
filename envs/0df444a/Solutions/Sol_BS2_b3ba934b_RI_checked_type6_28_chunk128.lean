-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_28_chunk128
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:46:08.226833+00:00
-- url     : https://prove2.me/submissions/87ed3046-74f1-4149-a5cc-c53d72d65b4b

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 128 64=true := by decide +kernel
