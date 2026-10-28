-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_31_chunk256
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:34:42.481124+00:00
-- url     : https://prove2.me/submissions/63650e1f-882d-4667-af1b-d49cbe291cbb

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 256 64=true := by decide +kernel
