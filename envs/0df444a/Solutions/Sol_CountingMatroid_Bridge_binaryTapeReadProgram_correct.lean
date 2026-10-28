-- Prove2me | solution 1 for CountingMatroid.Bridge.binaryTapeReadProgram_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T18:44:40.106774+00:00
-- url     : https://prove2.me/submissions/e7c5aff7-a92a-4ab6-a535-241eba1f78bf

import Definitions.Def_CountingMatroid_Bridge_BinaryTapeRead

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem solution {n : ℕ}
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 0 5) (xs : List Bool)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = xs) :
    ∃ t : ℕ,
      let out := execution CountingMatroid.Bridge.binaryTapeReadProgram O c bits t
      (out.control.val =
        (if xs.head? = some true then 5 else if xs.head? = some false then 4 else 1)) ∧
      out.registers 6 = xs ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + t := by
  cases xs with
  | nil =>
      refine ⟨1, ?_⟩
      simp [execution, machineStep, CountingMatroid.Bridge.binaryTapeReadProgram, hc, ho, h6]
  | cons b tail =>
      cases b <;> refine ⟨2, ?_⟩ <;>
        simp [execution, machineStep, CountingMatroid.Bridge.binaryTapeReadProgram, hc, ho, h6]
