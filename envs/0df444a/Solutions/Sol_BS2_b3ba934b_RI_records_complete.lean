-- Prove2me | solution 1 for BS2_b3ba934b_RI_records_complete
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:57:41.275979+00:00
-- url     : https://prove2.me/submissions/ce37694f-4465-4af5-985e-0359e5e3839e

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Mathlib.Tactic.FinCases
import Theorems.Thm_BS2_b3ba934b_RI_Batch_3bccebf24301
import Theorems.Thm_BS2_b3ba934b_RI_Batch_4bb724743bd9
import Theorems.Thm_BS2_b3ba934b_RI_Batch_9a07c7fecb86
import Theorems.Thm_BS2_b3ba934b_RI_checked_length5
import Theorems.Thm_BS2_b3ba934b_RI_checked_length6
import Theorems.Thm_BS2_b3ba934b_RI_checked_length7
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : ∀ xs∈ThreeBoundQ2.records,
    xs∈ThreeBoundNumeric.Endpoint40.records := by
  intro xs hx
  rw [← (BS2_b3ba934b_RI_Batch_3bccebf24301.1)]
  apply ThreeBoundRecordLookup.records_subset_of_checkLengths ThreeBoundEndpoint40Records.tree ?_ xs hx
  intro n
  fin_cases n
  · exact (BS2_b3ba934b_RI_Batch_9a07c7fecb86.1)
  · exact (BS2_b3ba934b_RI_Batch_9a07c7fecb86.2.1)
  · exact (BS2_b3ba934b_RI_Batch_9a07c7fecb86.2.2.1)
  · exact (BS2_b3ba934b_RI_Batch_9a07c7fecb86.2.2.2.1)
  · exact (BS2_b3ba934b_RI_Batch_4bb724743bd9.1)
  · exact BS2_b3ba934b_RI_checked_length5
  · exact BS2_b3ba934b_RI_checked_length6
  · exact BS2_b3ba934b_RI_checked_length7
