-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_27_chunk3840
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:45:53.299493+00:00
-- url     : https://prove2.me/submissions/385b4187-a6bd-4bf5-9488-e55ba0870088

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3840 64=true := by decide +kernel
