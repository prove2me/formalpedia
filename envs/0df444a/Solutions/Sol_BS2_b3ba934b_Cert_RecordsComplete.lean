-- Prove2me | solution 1 for BS2_b3ba934b_Cert_RecordsComplete
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:00:15.641981+00:00
-- url     : https://prove2.me/submissions/a3da2739-aad9-46d8-9bb3-5bf5c9952770

import Theorems.Thm_BS2_b3ba934b_RI_records_complete
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ∀ xs∈ThreeBoundQ2.records,
    xs∈ThreeBoundNumeric.Endpoint40.records := by
  exact BS2_b3ba934b_RI_records_complete
