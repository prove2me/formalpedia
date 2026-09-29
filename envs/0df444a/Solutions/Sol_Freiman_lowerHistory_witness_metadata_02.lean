-- Prove2me | solution 1 for Freiman.lowerHistory_witness_metadata_02
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T00:35:08.640179+00:00
-- url     : https://prove2.me/submissions/b7799003-1cde-4553-ad76-bd0f0c06f8fc

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : lowerHistoryWitnesses02.toList.map
    (fun w => (w.lowerBound, w.upperBound, w.rectangle)) =
  (lowerHistoryWitnessIds02.toList.zip ([2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,1,2,4,5,1,2,4,5,6,7,1,2,4,5,1,2,4,5,1,2,4,5,1,2,4,5,6,7,1,2,4,5,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,1,2,4,5,1,2,4,5,1,2,4,5,1,2,4,5,1,2,4,5,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3,3,0,3,0,3,0,3,0,3,0,3,0,3,0,3] : List ℕ)).map
    (fun z => (lowerHistoryBound z.1.1, lowerHistoryBound z.1.2,
      lowerHistoryRectangles[z.2]?.getD ⟨0,1,0,1⟩)) := by rfl
#print axioms solution
