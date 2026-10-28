-- Prove2me | solution 1 for CountingMatroid.Bridge.appendProgram_execution_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T04:28:47.857785+00:00
-- url     : https://prove2.me/submissions/bd45369e-c17b-4499-b304-6c590838ff1f

import Definitions.Def_CountingMatroidBridgeProgramAppend
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CountingMatroid.Bridge
open OAI.CommonBasesFPRAS

@[simp] theorem decode_shifted_state {s : ℕ} (q : Fin (s + 1)) :
    decodeProgramState (shiftedProgramState q) = q := by
  apply Fin.ext
  simp [decodeProgramState, shiftedProgramState]

theorem appendProgram_shift {s : ℕ} (P : Program 2 s) (q : Fin (s + 1)) :
    sampleThenProgram P (shiftedProgramState q) = shiftInstruction (P q) := by
  have hsmall : ¬ (shiftedProgramState q).val < 4 := by
    dsimp [shiftedProgramState]
    omega
  have hnotstart : (shiftedProgramState q).val ≠ 4 := by
    dsimp [shiftedProgramState]
    omega
  simp [sampleThenProgram, hsmall, hnotstart, shiftedProgramState]

theorem appendProgram_current_instruction {s : ℕ} (P : Program 2 s)
    (q : Fin (s + 6)) (hcontrol : q.val = 4 ∨ 5 ≤ q.val) :
    sampleThenProgram P q = shiftInstruction (P (decodeProgramState q)) := by
  rcases hcontrol with hfour | hlarge
  · have hc : q = ⟨4, by omega⟩ := Fin.ext hfour
    rw [hc]
    simp [sampleThenProgram, decodeProgramState]
  · let i : Fin (s + 1) := ⟨q.val - 5, by have := q.isLt; omega⟩
    have hc : q = shiftedProgramState i := by
      apply Fin.ext
      simpa [i, shiftedProgramState] using (Nat.sub_add_cancel hlarge).symm
    rw [hc]
    simp [appendProgram_shift, decode_shifted_state]

theorem decode_step_of_current_instruction {s n : ℕ} (Q : Program 2 (s + 5))
    (P : Program 2 s) (O : IndependenceOracle n) (bit : Bool)
    (c : MachineConfig 2 (s + 5))
    (hcurrent : Q c.control = shiftInstruction (P (decodeProgramState c.control))) :
    decodeProgramConfig (machineStep Q O bit c) =
      machineStep P O bit (decodeProgramConfig c) := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  cases output with
  | some value => rfl
  | none =>
      have hcurrent' : Q control = shiftInstruction (P (decodeProgramState control)) := by
        simpa using hcurrent
      simp only [machineStep, Option.isSome_none, ↓reduceIte, hcurrent']
      cases hp : P (decodeProgramState control) with
      | push i b next => simp [decodeProgramConfig, shiftInstruction, hp]
      | pop i empty zero one =>
          cases hstack : regs i with
          | nil => simp [decodeProgramConfig, shiftInstruction, hp, hstack]
          | cons b rest => cases b <;>
              simp [decodeProgramConfig, shiftInstruction, hp, hstack]
      | coin zero one => cases bit <;> simp [decodeProgramConfig, shiftInstruction, hp]
      | query which i no yes =>
          by_cases hlen : (regs i).length = n
          · have hbits : (fun j : Fin n => (regs i)[j.val]?.getD false) =
                (fun j : Fin n => (regs i)[j.val]) := by
              funext j
              simp [List.getElem?_eq_getElem (by rw [hlen]; exact j.isLt)]
            by_cases hquery : O which (fun j : Fin n => (regs i)[j.val]?.getD false) = true
            · have hraw : O which (fun j : Fin n => (regs i)[j.val]) = true := by
                simpa only [← hbits] using hquery
              simp [decodeProgramConfig, shiftInstruction, hp, hlen, hquery, hraw,
                decode_shifted_state]
            · have hraw : ¬ O which (fun j : Fin n => (regs i)[j.val]) = true := by
                simpa only [← hbits] using hquery
              simp [decodeProgramConfig, shiftInstruction, hp, hlen, hquery, hraw,
                decode_shifted_state]
          · simp [decodeProgramConfig, shiftInstruction, hp, hlen]
      | halt => simp [decodeProgramConfig, shiftInstruction, hp]

theorem appendProgram_machineStep_decode {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (bit : Bool) (c : MachineConfig 2 (s + 5))
    (hcontrol : c.control.val = 4 ∨ 5 ≤ c.control.val) :
    decodeProgramConfig (machineStep (sampleThenProgram P) O bit c) =
      machineStep P O bit (decodeProgramConfig c) := by
  apply decode_step_of_current_instruction
  exact appendProgram_current_instruction P c.control hcontrol

theorem appendProgram_step_control_valid {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (bit : Bool) (c : MachineConfig 2 (s + 5))
    (hcontrol : c.control.val = 4 ∨ 5 ≤ c.control.val) :
    (machineStep (sampleThenProgram P) O bit c).control.val = 4 ∨
      5 ≤ (machineStep (sampleThenProgram P) O bit c).control.val := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  cases output with
  | some value => exact hcontrol
  | none =>
    have hcontrol' : control.val = 4 ∨ 5 ≤ control.val := by simpa using hcontrol
    have hcurrent := appendProgram_current_instruction P control hcontrol
    have hcurrent' : sampleThenProgram P control =
        shiftInstruction (P (decodeProgramState control)) := by simpa using hcurrent
    simp only [machineStep, Option.isSome_none, ↓reduceIte, hcurrent']
    cases hp : P (decodeProgramState control) with
    | push i b next =>
        simp [shiftInstruction, shiftedProgramState] <;> omega
    | pop i empty zero one =>
        cases hstack : regs i with
        | nil => simp [shiftInstruction, shiftedProgramState, hstack, hcontrol'] <;> omega
        | cons b rest => cases b <;>
            simp [shiftInstruction, shiftedProgramState, hstack] <;> omega
    | coin zero one =>
        cases bit <;> simp [shiftInstruction, shiftedProgramState] <;> omega
    | query which i no yes =>
        by_cases hlen : (regs i).length = n
        · by_cases hquery : O which (fun j => (regs i)[j.val]?.getD false) = true
          · simp [shiftInstruction, shiftedProgramState, hlen, hquery]
            right
            split_ifs <;> simp [shiftedProgramState]
          · simp [shiftInstruction, shiftedProgramState, hlen, hquery]
            right
            split_ifs <;> simp [shiftedProgramState]
        · simp [shiftInstruction, shiftedProgramState, hlen, hcontrol'] <;> omega
    | halt => simp [shiftInstruction, shiftedProgramState, hcontrol'] <;> omega

theorem appendProgram_execution_control_valid {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 5)) (bits : ℕ → Bool)
    (t : ℕ) (hcontrol : c.control.val = 4 ∨ 5 ≤ c.control.val) :
    (execution (sampleThenProgram P) O c bits t).control.val = 4 ∨
      5 ≤ (execution (sampleThenProgram P) O c bits t).control.val := by
  induction t with
  | zero => exact hcontrol
  | succ t ih =>
      change (machineStep (sampleThenProgram P) O (bits t)
        (execution (sampleThenProgram P) O c bits t)).control.val = 4 ∨ _
      exact appendProgram_step_control_valid P O (bits t) _ ih

theorem appendProgram_execution_decode {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 5))
    (bits : ℕ → Bool) (t : ℕ)
    (hcontrol : c.control.val = 4) :
    decodeProgramConfig
      (execution (sampleThenProgram P) O c bits t) =
      execution P O (programStartConfig c) bits t := by
  induction t with
  | zero =>
      rcases c with ⟨regs, control, output, calls, ops⟩
      have hc : control = ⟨4, by omega⟩ := Fin.ext hcontrol
      rw [hc]
      rfl
  | succ t ih =>
      change decodeProgramConfig
          (machineStep (sampleThenProgram P) O (bits t)
            (execution (sampleThenProgram P) O c bits t)) = _
      rw [appendProgram_machineStep_decode _ _ _ _
        (appendProgram_execution_control_valid P O c bits t (Or.inl hcontrol))]
      rw [ih]
      rfl

end CountingMatroid.Bridge

abbrev solution := @CountingMatroid.Bridge.appendProgram_execution_decode
