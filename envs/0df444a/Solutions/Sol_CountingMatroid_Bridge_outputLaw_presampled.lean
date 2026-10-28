-- Prove2me | solution 1 for CountingMatroid.Bridge.outputLaw_presampled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:39:44.229672+00:00
-- url     : https://prove2.me/submissions/df2266e3-266d-46cb-994b-a70903e12e8d

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Bridge_algorithmLaw_presampled

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- Exact output-and-charge law, including early exits and aborts. The
reported charges remain the source charges, excluding eager sampling costs. -/
theorem solution (solver : Subroutines.FeasibilityImplementation)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams) :
    outputLaw solver n r o₁ o₂ p =
      (fairTape ((Program.schedule n p).val.repetitions * blockLength n r p)).map
        (presampledOutcome solver n r o₁ o₂ p) := by
  change (algorithmLaw solver n r o₁ o₂ p).map
    (fun run => (run.val, ExecutionCost.mk (Subroutines.oracleCalls run)
      (Subroutines.otherSteps run) (run.cost Op.fairBit))) = _
  rw [algorithmLaw_presampled, PMF.map_comp]
  rfl
