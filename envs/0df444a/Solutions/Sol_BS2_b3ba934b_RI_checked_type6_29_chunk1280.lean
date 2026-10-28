-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_29_chunk1280
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:39:14.923417+00:00
-- url     : https://prove2.me/submissions/9997d3b4-457e-4a3e-a8bc-bdb54491cfd9

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1280 64=true := by decide +kernel
