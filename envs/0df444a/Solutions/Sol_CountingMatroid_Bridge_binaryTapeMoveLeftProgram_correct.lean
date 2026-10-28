-- Prove2me | solution 1 for CountingMatroid.Bridge.binaryTapeMoveLeftProgram_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T18:58:05.151829+00:00
-- url     : https://prove2.me/submissions/b27f49c8-9869-4d53-aa69-f370f9be719b

import Definitions.Def_CountingMatroid_Bridge_BinaryTapeMoveLeft

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem solution {n : ℕ}
    (O : IndependenceOracle n) (bits : ℕ → Bool) (c : MachineConfig 0 17)
    (left right : List Bool) (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = left) (h7 : c.registers 7 = right) :
    let out := execution CountingMatroid.Bridge.binaryTapeMoveLeftProgram O c bits 4
    out.control.val = (if right.headD false then
        (if left.headD false then 15 else 14)
      else if left.headD false then 13 else 12) ∧
      out.registers 6 = left.drop 1 ∧
      out.registers 7 = (left.headD false) :: (right.headD false) :: (right.drop 1) ∧
      out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + 4 := by
  cases right with
  | nil =>
      cases left with
      | nil => simp [execution, machineStep, CountingMatroid.Bridge.binaryTapeMoveLeftProgram, hc, ho, h6, h7]
      | cons a leftTail =>
          cases a <;>
            simp [execution, machineStep, CountingMatroid.Bridge.binaryTapeMoveLeftProgram, hc, ho, h6, h7]
  | cons b rightTail =>
      cases left with
      | nil =>
          cases b <;>
            simp [execution, machineStep, CountingMatroid.Bridge.binaryTapeMoveLeftProgram, hc, ho, h6, h7]
      | cons a leftTail =>
          cases b <;> cases a <;>
            simp [execution, machineStep, CountingMatroid.Bridge.binaryTapeMoveLeftProgram, hc, ho, h6, h7]
