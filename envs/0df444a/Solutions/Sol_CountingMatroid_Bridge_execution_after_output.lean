-- Prove2me | solution 1 for CountingMatroid.Bridge.execution_after_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:17:44.675679+00:00
-- url     : https://prove2.me/submissions/8364fff5-fcc1-47b7-a19e-984e02c96797

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid.Bridge

/-- The mission execution freezes the entire configuration after output,
including its actual cost counters. -/
theorem solution {k s n : ℕ} (P : OAI.CommonBasesFPRAS.Program k s)
    (O : OAI.CommonBasesFPRAS.IndependenceOracle n)
    (c : OAI.CommonBasesFPRAS.MachineConfig k s) (bits : ℕ → Bool)
    {t B : ℕ} (ht : t ≤ B)
    (h : (OAI.CommonBasesFPRAS.execution P O c bits t).output.isSome) :
    OAI.CommonBasesFPRAS.execution P O c bits B =
      OAI.CommonBasesFPRAS.execution P O c bits t := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.add_succ, OAI.CommonBasesFPRAS.execution, ih]
    simp [OAI.CommonBasesFPRAS.machineStep, h]
