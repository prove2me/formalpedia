-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_length7
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:49:23.660238+00:00
-- url     : https://prove2.me/submissions/69a01236-d3a0-4b05-b720-2a14c48e98e6

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Theorems.Thm_BS2_b3ba934b_RI_activeTypes7_eq
import Theorems.Thm_BS2_b3ba934b_RI_checked_length7_coverage_tail000
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree 7=true := by
  apply ThreeBoundRecordLookup.checkLength_of_active
  rw [BS2_b3ba934b_RI_activeTypes7_eq]
  exact BS2_b3ba934b_RI_checked_length7_coverage_tail000
