-- Prove2me | solution 1 for CountingMatroid.Bridge.algorithmLaw_presampled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:35:43.96652+00:00
-- url     : https://prove2.me/submissions/ecf72135-b778-4990-a88f-e838bfed832d

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Bridge_fairTape_splitBlocks

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- The original estimator law is the pushforward of a single flat fair tape. -/
theorem solution (solver : Subroutines.FeasibilityImplementation)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams) :
    algorithmLaw solver n r o₁ o₂ p =
      (fairTape ((Program.schedule n p).val.repetitions * blockLength n r p)).map
        (fun bits => Program.estimate solver n r o₁ o₂ p
          (blockTape (splitBlocks (blockLength n r p)
            (Program.schedule n p).val.repetitions bits))) := by
  unfold algorithmLaw
  change (fairBlocks _ _).map _ = _
  rw [← fairTape_splitBlocks, PMF.map_comp]
  rfl
