-- Prove2me | solution 1 for CountingMatroid.Bridge.binaryTapeMoveRightProgram_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T18:51:22.750408+00:00
-- url     : https://prove2.me/submissions/5bd15ab1-005a-4f3e-9070-5c3d3671847d

import Definitions.Def_CountingMatroid_Bridge_BinaryTapeMoveRight

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem solution {n : ℕ}
    (O : IndependenceOracle n) (bits : ℕ → Bool) (c : MachineConfig 0 6)
    (left right : List Bool) (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = left) (h7 : c.registers 7 = right) :
    let out := execution CountingMatroid.Bridge.binaryTapeMoveRightProgram O c bits 2
    out.control.val = (if right.head? = some true then 6 else 5) ∧
      out.registers 6 = (right.headD false) :: left ∧
      out.registers 7 = right.drop 1 ∧
      out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + 2 := by
  cases right with
  | nil =>
      simp [execution, machineStep, CountingMatroid.Bridge.binaryTapeMoveRightProgram, hc, ho, h6, h7]
  | cons b tail =>
      cases b <;>
        simp [execution, machineStep, CountingMatroid.Bridge.binaryTapeMoveRightProgram, hc, ho, h6, h7]
