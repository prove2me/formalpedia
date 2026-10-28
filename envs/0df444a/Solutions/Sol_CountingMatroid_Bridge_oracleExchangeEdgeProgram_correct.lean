-- Prove2me | solution 1 for CountingMatroid.Bridge.oracleExchangeEdgeProgram_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T15:18:27.723813+00:00
-- url     : https://prove2.me/submissions/863f21e2-ceaa-4e29-8190-dafc2c5a8bb4

import Definitions.Def_CountingMatroid_Bridge_OracleExchangeProgram

set_option autoImplicit false
set_option maxHeartbeats 800000

open OAI.CommonBasesFPRAS
open CountingMatroid.Bridge

/-- Two guarded independence-oracle tests. The fixed program always makes
both calls and reaches state 12 exactly when an enabled candidate is accepted. -/
theorem solution {n : ℕ}
    (O : OAI.CommonBasesFPRAS.IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 16) (forward reverse : Bool)
    (qForward qReverse : Fin n → Bool)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = [forward]) (h7 : c.registers 7 = [reverse])
    (h8 : c.registers 8 = List.ofFn qForward)
    (h9 : c.registers 9 = List.ofFn qReverse) :
    let out := execution oracleExchangeEdgeProgram O c bits 4
    out.control.val =
        (if (forward && O false qForward) || (reverse && O true qReverse)
          then 12 else 10) ∧
    out.registers 6 = [] ∧ out.registers 7 = [] ∧
    out.registers 8 = List.ofFn qForward ∧ out.registers 9 = List.ofFn qReverse ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls + 2 ∧
    out.bitOperations = c.bitOperations + (4 * n + 4) := by
  have hlen8 : (c.registers 8).length = n := by rw [h8]; simp
  have hlen9 : (c.registers 9).length = n := by rw [h9]; simp
  have hread8 : (fun i : Fin n => (c.registers 8)[i.val]?.getD false) = qForward := by
    funext i
    rw [h8]
    simp
  have hread9 : (fun i : Fin n => (c.registers 9)[i.val]?.getD false) = qReverse := by
    funext i
    rw [h9]
    simp
  cases forward <;> cases reverse <;>
    cases hf : O false qForward <;> cases hr : O true qReverse <;>
    simp [execution, machineStep, oracleExchangeEdgeProgram, hc, ho,
      h6, h7, h8, h9, hlen8, hlen9, hread8, hread9, hf, hr] <;> omega

#print axioms solution
