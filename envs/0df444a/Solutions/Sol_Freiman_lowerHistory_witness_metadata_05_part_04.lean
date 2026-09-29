-- Prove2me | solution 1 for Freiman.lowerHistory_witness_metadata_05_part_04
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T08:59:16.357229+00:00
-- url     : https://prove2.me/submissions/019d9d5c-0a46-4e9a-8b3b-1bf536a49bc1

import Definitions.Def_Freiman_lowerHistoryWitnesses05
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem solution : ((lowerHistoryWitnesses05.toList.drop 150).take 50).map (fun w : CertWitness => (w.lowerBound,w.upperBound,w.rectangle)) =
  (((lowerHistoryWitnessIds05.toList.zip ([2,4,5,1,2,4,5,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,6] : List ℕ)).drop 150).take 50).map (fun z : (ℕ × ℕ) × ℕ => (lowerHistoryBound z.1.1,lowerHistoryBound z.1.2,lowerHistoryRectangles[z.2]?.getD ⟨0,1,0,1⟩)) := by rfl
#print axioms solution
