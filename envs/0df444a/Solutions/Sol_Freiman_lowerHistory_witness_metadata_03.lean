-- Prove2me | solution 1 for Freiman.lowerHistory_witness_metadata_03
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T00:35:16.852489+00:00
-- url     : https://prove2.me/submissions/4cf5f9cd-7d0b-45d4-9eb5-3f20a7544ccf

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : lowerHistoryWitnesses03.toList.map
    (fun w => (w.lowerBound, w.upperBound, w.rectangle)) =
  (lowerHistoryWitnessIds03.toList.zip ([0,3,0,3,3,0,3,0,3,3,0,3,0,3,0,3,0,3,0,3,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,3,0,3,0,3,0,3,0,3,0,3,0,3,3,0,3,0,3,0,3,0,3,3,0,3,0,3,0,3,0,3,0,3,0,3,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,1,2,4,5,1,2,4,5,1,2,4,5,6,7,1,2,4,5,1,2,4,5,1,2,4,5,6,7,1,2,4,5,1,2,4,5,1,2,4,5,1,2,4,5,1,2,4,5,6,7,1,2,4,5,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2] : List ℕ)).map
    (fun z => (lowerHistoryBound z.1.1, lowerHistoryBound z.1.2,
      lowerHistoryRectangles[z.2]?.getD ⟨0,1,0,1⟩)) := by rfl
#print axioms solution
