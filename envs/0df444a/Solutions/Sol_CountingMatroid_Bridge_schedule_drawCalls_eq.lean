-- Prove2me | solution 1 for CountingMatroid.Bridge.schedule_drawCalls_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:28:38.161628+00:00
-- url     : https://prove2.me/submissions/edcd3abe-e987-4728-846e-81390011a603

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- The concrete schedule's draw count, without any tape-coverage assumption. -/
theorem solution (n : ℕ) (p : InputParams) :
    let s := (Program.schedule n p).val
    s.drawCalls = 3 * s.L * (s.restartCap + s.observations) := by
  rfl
