-- Prove2me | solution 1 for Freiman.lowerHistory_witness_metadata_04
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T00:35:57.114682+00:00
-- url     : https://prove2.me/submissions/cbefe321-715e-4d43-9776-d4d593abb347

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : lowerHistoryWitnesses04.toList.map
    (fun w => (w.lowerBound, w.upperBound, w.rectangle)) =
  (lowerHistoryWitnessIds04.toList.zip ([4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,1,2,4,5,5,1] : List ℕ)).map
    (fun z => (lowerHistoryBound z.1.1, lowerHistoryBound z.1.2,
      lowerHistoryRectangles[z.2]?.getD ⟨0,1,0,1⟩)) := by rfl
#print axioms solution
