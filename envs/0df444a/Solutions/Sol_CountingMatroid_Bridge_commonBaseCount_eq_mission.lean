-- Prove2me | solution 1 for CountingMatroid.Bridge.commonBaseCount_eq_mission
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:33:43.925852+00:00
-- url     : https://prove2.me/submissions/a9185c42-9b10-4c73-9725-af450bf7785f

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- Both developments count exactly the same finite family of common bases. -/
theorem solution {n : ℕ} (M₁ M₂ : Matroid (Fin n)) :
    commonBaseCount M₁ M₂ = OAI.CommonBasesFPRAS.commonBaseCount M₁ M₂ := by
  classical
  unfold commonBaseCount commonBases OAI.CommonBasesFPRAS.commonBaseCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
