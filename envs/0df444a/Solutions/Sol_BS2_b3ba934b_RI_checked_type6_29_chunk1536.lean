-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_29_chunk1536
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:33:20.255745+00:00
-- url     : https://prove2.me/submissions/05f849e1-be3c-4268-a14c-0934d58a71e0

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1536 64=true := by decide +kernel
