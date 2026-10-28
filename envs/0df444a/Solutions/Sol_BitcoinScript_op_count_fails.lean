-- Prove2me | solution 1 for BitcoinScript.op_count_fails
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T05:50:54.340357+00:00
-- url     : https://prove2.me/submissions/7ad18def-70ca-4343-b080-574da81688ae

import Definitions.Def_BitcoinScript
import Theorems.Thm_BitcoinScript_execOp_opCount

open BitcoinScript

private theorem step_push_opCount (f : Flags) (o : Oracle) (s s' : State) (d : Bytes)
    (h : step f o s (.push d) = some s') : s'.opCount = s.opCount := by
  unfold step at h
  dsimp only at h
  repeat' split at h
  all_goals (cases h; try rfl)

/-- One opcode step: a counted opcode (above `OP_16`) raises `nOpCount` by at least one, and the
result's count is either the input's or within the limit. -/
private theorem step_op_opCount (f : Flags) (o : Oracle) (s s' : State) (c : Byte)
    (h : step f o s (.op c) = some s') :
    s.opCount + (if OP_16 < c then 1 else 0) ≤ s'.opCount ∧
      (s'.opCount = s.opCount ∨ s'.opCount ≤ MAX_OPS_PER_SCRIPT) := by
  unfold step at h
  dsimp only at h
  by_cases hc : OP_16 < c
  · rw [if_pos hc]
    simp only [hc, decide_true, Bool.true_and, decide_eq_true_eq, ite_true] at h
    by_cases h1 : MAX_OPS_PER_SCRIPT < s.opCount + 1
    · rw [if_pos h1] at h; cases h
    · rw [if_neg h1] at h
      by_cases h2 : isDisabled c = true
      · rw [if_pos h2] at h; cases h
      · rw [if_neg h2] at h
        split at h
        · split at h
          · cases h
          · rename_i hcond x sx hex
            split at h
            · cases h
            · have hoc := BitcoinScript.execOp_opCount f o _ c _ sx hex
              simp only at hoc
              cases h
              constructor <;> omega
        · split at h
          · cases h
          · cases h
            constructor <;> simp <;> omega
  · rw [if_neg hc]
    simp only [hc, decide_false, Bool.false_and, Bool.false_eq_true, ite_false] at h
    by_cases h2 : isDisabled c = true
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      split at h
      · split at h
        · cases h
        · rename_i hcond x sx hex
          split at h
          · cases h
          · have hoc := BitcoinScript.execOp_opCount f o _ c _ sx hex
            cases h
            constructor <;> omega
      · split at h
        · cases h
        · cases h
          constructor <;> omega

/-- The loop invariant: the count grows by at least the number of counted opcodes, and ends
either unchanged or within the limit. -/
private theorem run_opCount (f : Flags) (o : Oracle) :
    ∀ (script : Script) (s s' : State), run f o s script = some s' →
      s.opCount + BitcoinScript.opsIn script ≤ s'.opCount ∧
      (s'.opCount = s.opCount ∨ s'.opCount ≤ MAX_OPS_PER_SCRIPT)
  | [], s, s', h => by
    unfold run at h
    split at h
    · cases h; simp [BitcoinScript.opsIn]
    · cases h
  | i :: rest, s, s', h => by
    unfold run at h
    cases hstep : step f o s i with
    | none => rw [hstep] at h; cases h
    | some s1 =>
      rw [hstep] at h
      have ih := run_opCount f o rest s1 s' h
      cases i with
      | push d =>
        have e := step_push_opCount f o s s1 d hstep
        simp only [BitcoinScript.opsIn] at *
        constructor <;> omega
      | op c =>
        have hs := step_op_opCount f o s s1 c hstep
        simp only [BitcoinScript.opsIn] at *
        by_cases hc : OP_16 < c
        · rw [if_pos hc] at hs ⊢; constructor <;> omega
        · rw [if_neg hc] at hs ⊢; constructor <;> omega

/-- A script with more than `MAX_OPS_PER_SCRIPT` counted opcodes never evaluates successfully,
from any starting stack. -/
theorem solution (f : Flags) (o : Oracle) (stack : List Bytes) (script : Script)
    (h : BitcoinScript.MAX_OPS_PER_SCRIPT < BitcoinScript.opsIn script) :
    BitcoinScript.evalScript f o stack script = none := by
  unfold evalScript
  cases hr : run f o (State.initial stack) script with
  | none => rfl
  | some s' =>
    exfalso
    have := run_opCount f o script _ s' hr
    simp only [State.initial] at this
    omega
