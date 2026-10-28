-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_29_chunk1600
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:33:32.205004+00:00
-- url     : https://prove2.me/submissions/d632f7b9-240b-456c-a090-5d8e7489b047

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1600 64=true := by decide +kernel
