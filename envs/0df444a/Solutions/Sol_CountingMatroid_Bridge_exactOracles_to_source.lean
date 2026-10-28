-- Prove2me | solution 1 for CountingMatroid.Bridge.exactOracles_to_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:34:57.156174+00:00
-- url     : https://prove2.me/submissions/ea71cfdb-b55d-4be6-9dfb-22907e7d3bdd

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- Split the mission's selector oracle into the source's two exact oracles. -/
theorem solution {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (O : OAI.CommonBasesFPRAS.IndependenceOracle n)
    (h : OAI.CommonBasesFPRAS.ExactOracles M₁ M₂ O) :
    ExactOracle M₁ (O false) ∧ ExactOracle M₂ (O true) := by
  classical
  constructor
  · intro q
    apply Bool.eq_iff_iff.mpr
    change (O false q = true ↔ decide (M₁.Indep (decode q)) = true)
    rw [decide_eq_true_eq]
    exact h false q
  · intro q
    apply Bool.eq_iff_iff.mpr
    change (O true q = true ↔ decide (M₂.Indep (decode q)) = true)
    rw [decide_eq_true_eq]
    exact h true q
