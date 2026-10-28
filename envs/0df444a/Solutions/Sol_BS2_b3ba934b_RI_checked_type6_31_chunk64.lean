-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_31_chunk64
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:39:14.746123+00:00
-- url     : https://prove2.me/submissions/b80264b3-36c5-4a48-8c70-c12bbdb4cd79

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 64 64=true := by decide +kernel
