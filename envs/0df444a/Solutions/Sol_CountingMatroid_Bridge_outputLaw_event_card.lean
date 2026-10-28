-- Prove2me | solution 1 for CountingMatroid.Bridge.outputLaw_event_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:43:55.396169+00:00
-- url     : https://prove2.me/submissions/0b9d52cf-97c1-46bf-9a88-f3dea634f8d6

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Analysis_SingleRunAccuracy_fairTape_event_card
import Theorems.Thm_CountingMatroid_Bridge_outputLaw_presampled

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- The source probability of any output event equals its count among flat
finite Boolean tapes divided by the number of such tapes. -/
theorem solution (solver : Subroutines.FeasibilityImplementation)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (event : Set (ℚ × ExecutionCost)) :
    let K := (Program.schedule n p).val.repetitions * blockLength n r p
    (outputLaw solver n r o₁ o₂ p).toOuterMeasure event =
      (Set.ncard {bits : List Bool | bits.length = K ∧
        presampledOutcome solver n r o₁ o₂ p bits ∈ event} : ENNReal) *
        (1 / 2 : ENNReal)^K := by
  dsimp only
  rw [outputLaw_presampled, PMF.toOuterMeasure_map_apply,
    Analysis.SingleRunAccuracy.fairTape_event_card]
  rfl
