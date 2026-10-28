-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_31_chunk0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:39:14.772285+00:00
-- url     : https://prove2.me/submissions/df38e869-1038-4dee-b77a-2f2d57d7f475

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 0 64=true := by decide +kernel
