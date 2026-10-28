-- Prove2me | solution 1 for CountingMatroid.Bridge.polynomial_source_bound_to_mission
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:37:54.985632+00:00
-- url     : https://prove2.me/submissions/1d9560ab-543a-4560-99b5-17502ad902e4

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Bridge_source_size_le_mission_size

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- Any polynomial source-size estimate transfers to the original mission's
input convention with only a constant-factor change of coefficient. -/
theorem solution (C d n r : ℕ) (p : InputParams) :
    C * (n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
      binaryNatLength (Nat.ceil p.δ⁻¹) + 1)^d ≤
    OAI.CommonBasesFPRAS.resourceBound (C * 6^d) d n r p.ε p.δ := by
  calc
    _ ≤ C * (6 * (1 + n + OAI.CommonBasesFPRAS.inputLength n r p.ε p.δ +
        Nat.ceil p.ε⁻¹ + Nat.clog 2 (Nat.ceil p.δ⁻¹)))^d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left (source_size_le_mission_size n r p) d)
    _ = _ := by unfold OAI.CommonBasesFPRAS.resourceBound; rw [mul_pow, mul_assoc]
