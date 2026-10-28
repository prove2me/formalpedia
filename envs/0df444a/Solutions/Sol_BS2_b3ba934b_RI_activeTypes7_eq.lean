-- Prove2me | solution 1 for BS2_b3ba934b_RI_activeTypes7_eq
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:46:08.206461+00:00
-- url     : https://prove2.me/submissions/e7af2aa1-47ab-49aa-9963-a17e226d48f6

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem solution : ThreeBoundRecordLookup.activeTypes 7 = [
[5,5,5,5,5,5,5]] := by decide +kernel
