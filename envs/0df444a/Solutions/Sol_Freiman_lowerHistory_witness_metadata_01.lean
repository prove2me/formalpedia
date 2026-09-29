-- Prove2me | solution 1 for Freiman.lowerHistory_witness_metadata_01
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T01:04:03.105035+00:00
-- url     : https://prove2.me/submissions/a51a56d4-89a3-4d84-91d1-8a74047ba213

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem solution : lowerHistoryWitnesses01.toList.map
    (fun w => (w.lowerBound, w.upperBound, w.rectangle)) =
  (lowerHistoryWitnessIds01.toList.zip ([1,2,4,1,2,4,7,1,2,4,1,2,4,7,1,2,4,5,1,2,4,5,6,7,1,2,4,5,1,2,4,5,1,2,4,5,1,2,4,5,1,2,4,5,6,7,1,2,4,5,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,1,2,4,5,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,1,2,4,5,0,3,1,2,4,5,1,2,4,5,6,7,1,2,4,5,1,2,4,5,1,2,4,5,1,2,4,5,6,7,1,2,4,5,1,2,4,5,6,7,1] : List ℕ)).map
    (fun z => (lowerHistoryBound z.1.1, lowerHistoryBound z.1.2,
      lowerHistoryRectangles[z.2]?.getD ⟨0,1,0,1⟩)) := by rfl
#print axioms solution
