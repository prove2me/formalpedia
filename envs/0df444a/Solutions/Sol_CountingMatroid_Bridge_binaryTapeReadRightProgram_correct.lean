-- Prove2me | solution 1 for CountingMatroid.Bridge.binaryTapeReadRightProgram_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T19:30:08.962992+00:00
-- url     : https://prove2.me/submissions/bdc23d7f-502b-4249-b52c-e08fc7b380b1

import Definitions.Def_CountingMatroid_Bridge_BinaryTapeReadRight
import Definitions.Def_CountingMatroid_Bridge_BinaryTapeSemantics
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid.Bridge OAI.CommonBasesFPRAS

theorem solution {n : ℕ}
    (O : IndependenceOracle n) (bits : ℕ → Bool) (c : MachineConfig 1 5)
    (left right : List Bool) (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = left) (h7 : c.registers 7 = right) :
    ∃ t : ℕ,
      let out := execution binaryTapeReadRightProgram O c bits t
      out.control.val = (if right.head? = some true then 5
        else if right.head? = some false then 4 else 1) ∧
      binaryTapeAt (out.registers 6) (out.registers 7) (.right 0) =
        binaryTapeAt left right (.right 0) ∧
      out.registers 6 = left ∧ out.registers 7 = right ∧
      out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + t := by
  cases right with
  | nil =>
      refine ⟨1, ?_⟩
      simp [execution, machineStep, binaryTapeReadRightProgram, hc, ho, h6, h7,
        binaryTapeAt, binaryStackRead]
  | cons b tail =>
      cases b <;> refine ⟨2, ?_⟩ <;>
        simp [execution, machineStep, binaryTapeReadRightProgram, hc, ho, h6, h7,
          binaryTapeAt, binaryStackRead]
