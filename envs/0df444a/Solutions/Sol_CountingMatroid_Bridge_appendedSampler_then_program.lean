-- Prove2me | solution 1 for CountingMatroid.Bridge.appendedSampler_then_program
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T04:47:11.909074+00:00
-- url     : https://prove2.me/submissions/8313c149-357a-4c28-bd80-9318894a9fac

import Definitions.Def_CountingMatroidBridgeSamplerContinuation
import Theorems.Thm_CountingMatroid_Bridge_appendProgram_execution_decode
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CountingMatroid.Bridge
open OAI.CommonBasesFPRAS

@[simp] theorem appendedProgram_at0 {s : ℕ} (P : Program 2 s) :
    sampleThenProgram P (0 : Fin (s + 6)) =
      .pop 8 (liftedSampleState 4) (liftedSampleState 1) (liftedSampleState 1) := by
  simp [sampleThenProgram, liftSampleInstruction, balancedSampler, liftedSampleState]
  <;> omega

theorem appendedProgram_at1_constructor {s : ℕ} (P : Program 2 s) :
    sampleThenProgram P (⟨1, by omega⟩ : Fin (s + 6)) =
      .coin (liftedSampleState 2) (liftedSampleState 3) := by
  simp [sampleThenProgram, liftSampleInstruction, balancedSampler, liftedSampleState]

@[simp] theorem appendedProgram_at1 {s : ℕ} (P : Program 2 s) :
    sampleThenProgram P (1 : Fin (s + 6)) =
      .coin (liftedSampleState 2) (liftedSampleState 3) := by
  have hq : (1 : Fin (s + 6)) = (⟨1, by omega⟩ : Fin (s + 6)) := by
    apply Fin.ext
    simp [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (by omega : (1 : ℕ) < s + 6)]
  rw [hq]
  exact appendedProgram_at1_constructor P

theorem appendedProgram_at2_constructor {s : ℕ} (P : Program 2 s) :
    sampleThenProgram P (⟨2, by omega⟩ : Fin (s + 6)) =
      .push 9 false (liftedSampleState 0) := by
  simp [sampleThenProgram, liftSampleInstruction, balancedSampler, liftedSampleState]

@[simp] theorem appendedProgram_at2 {s : ℕ} (P : Program 2 s) :
    sampleThenProgram P (2 : Fin (s + 6)) =
      .push 9 false (liftedSampleState 0) := by
  have hq : (2 : Fin (s + 6)) = (⟨2, by omega⟩ : Fin (s + 6)) := by
    apply Fin.ext
    simp [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (by omega : (2 : ℕ) < s + 6)]
  rw [hq]
  exact appendedProgram_at2_constructor P

theorem appendedProgram_at3_constructor {s : ℕ} (P : Program 2 s) :
    sampleThenProgram P (⟨3, by omega⟩ : Fin (s + 6)) =
      .push 9 true (liftedSampleState 0) := by
  simp [sampleThenProgram, liftSampleInstruction, balancedSampler, liftedSampleState]

@[simp] theorem appendedProgram_at3 {s : ℕ} (P : Program 2 s) :
    sampleThenProgram P (3 : Fin (s + 6)) =
      .push 9 true (liftedSampleState 0) := by
  have hq : (3 : Fin (s + 6)) = (⟨3, by omega⟩ : Fin (s + 6)) := by
    apply Fin.ext
    simp [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (by omega : (3 : ℕ) < s + 6)]
  rw [hq]
  exact appendedProgram_at3_constructor P

@[simp] theorem appendedProgram_lifted1 {s : ℕ} (P : Program 2 s) :
    sampleThenProgram P (liftedSampleState (1 : Fin 5)) =
      .coin (liftedSampleState 2) (liftedSampleState 3) := by
  have hq : liftedSampleState (1 : Fin 5) = (⟨1, by omega⟩ : Fin (s + 6)) := by
    apply Fin.ext
    simp [liftedSampleState, Fin.coe_ofNat_eq_mod]
  rw [hq]
  exact appendedProgram_at1 P

@[simp] theorem appendedProgram_lifted2 {s : ℕ} (P : Program 2 s) :
    sampleThenProgram P (liftedSampleState (2 : Fin 5)) =
      .push 9 false (liftedSampleState 0) := by
  have hq : liftedSampleState (2 : Fin 5) = (⟨2, by omega⟩ : Fin (s + 6)) := by
    apply Fin.ext
    simp [liftedSampleState, Fin.coe_ofNat_eq_mod]
  rw [hq]
  exact appendedProgram_at2 P

@[simp] theorem appendedProgram_lifted3 {s : ℕ} (P : Program 2 s) :
    sampleThenProgram P (liftedSampleState (3 : Fin 5)) =
      .push 9 true (liftedSampleState 0) := by
  have hq : liftedSampleState (3 : Fin 5) = (⟨3, by omega⟩ : Fin (s + 6)) := by
    apply Fin.ext
    simp [liftedSampleState, Fin.coe_ofNat_eq_mod]
  rw [hq]
  exact appendedProgram_at3 P

theorem appended_execution_add_steps {k s n : ℕ} (P : Program k s)
    (O : IndependenceOracle n) (c : MachineConfig k s) (bits : ℕ → Bool)
    (a b : ℕ) :
    execution P O c bits (a + b) =
      execution P O (execution P O c bits a) (fun t => bits (a + t)) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
      change machineStep P O (bits (a + b)) (execution P O c bits (a + b)) = _
      rw [ih]
      rfl

theorem appendedSampler_cycle {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 5))
    (bits : ℕ → Bool) (b : Bool) (rest : List Bool)
    (hcontrol : c.control = 0) (houtput : c.output = none)
    (hcounter : c.registers 8 = b :: rest) :
    execution (sampleThenProgram P) O c bits 3 =
      { c with
        registers := Function.update (Function.update c.registers 8 rest) 9
          (bits 1 :: c.registers 9)
        control := 0
        bitOperations := c.bitOperations + 3 } := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  have hc : control = (0 : Fin (s + 6)) := by simpa using hcontrol
  have ho : output = none := by simpa using houtput
  have hcounter' : regs 8 = b :: rest := by simpa using hcounter
  subst control
  subst output
  cases hbit : bits 1 <;>
    simp [execution, machineStep, appendedProgram_at0, appendedProgram_at1,
      appendedProgram_at2, appendedProgram_at3, appendedProgram_at1_constructor,
      appendedProgram_at2_constructor, appendedProgram_at3_constructor, appendedProgram_lifted1,
      appendedProgram_lifted2, appendedProgram_lifted3, hcounter', hbit, Function.update,
      liftedSampleState, Nat.add_assoc]

theorem appendedSampler_prefix {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 5))
    (bits : ℕ → Bool) (K m : ℕ) (hm : m ≤ K) :
    execution (sampleThenProgram P) O (appendedSamplingConfig c bits K 0)
      bits (3 * m) = appendedSamplingConfig c bits K m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hrem : K - m = (K - (m + 1)) + 1 := by omega
      rw [show 3 * (m + 1) = 3 * m + 3 by omega,
        appended_execution_add_steps, ih (by omega)]
      have hcounter : (appendedSamplingConfig c bits K m).registers 8 =
          false :: List.replicate (K - (m + 1)) false := by
        simp [appendedSamplingConfig, hrem, List.replicate_succ]
      rw [appendedSampler_cycle P O _ (fun j => bits (3 * m + j)) false _ rfl rfl hcounter]
      simp [appendedSamplingConfig, sampledStack, Function.update, Nat.mul_add,
        Nat.add_assoc]
      funext i
      by_cases h8 : i = 8 <;> by_cases h9 : i = 9 <;> simp_all [Function.update]

theorem appendedSampler_exit {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 5))
    (bits : ℕ → Bool) (K : ℕ) :
    machineStep (sampleThenProgram P) O false (appendedSamplingConfig c bits K K) =
      appendedSamplerBoundary c bits K := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp [machineStep, liftedSampleState, appendedSamplerBoundary,
    appendedSamplingConfig, Function.update, Nat.add_assoc]
  all_goals try apply Fin.ext
  all_goals rfl

theorem appendedSampler_done {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 5))
    (bits : ℕ → Bool) (K : ℕ) :
    execution (sampleThenProgram P) O (appendedSamplingConfig c bits K 0)
      bits (3 * K + 1) = appendedSamplerBoundary c bits K := by
  rw [appended_execution_add_steps (a := 3 * K) (b := 1)]
  rw [appendedSampler_prefix P O c bits K K (by omega)]
  change machineStep (sampleThenProgram P) O (bits (3 * K))
      (appendedSamplingConfig c bits K K) = appendedSamplerBoundary c bits K
  exact appendedSampler_exit P O c bits K

theorem appendedSampler_then_program {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s + 5))
    (bits : ℕ → Bool) (K t : ℕ) :
    decodeProgramConfig
      (execution (sampleThenProgram P) O (appendedSamplingConfig c bits K 0)
        bits (3 * K + 1 + t)) =
      execution P O (programStartConfig (appendedSamplerBoundary c bits K))
        (fun j => bits (3 * K + 1 + j)) t := by
  rw [show 3 * K + 1 + t = (3 * K + 1) + t by omega,
    appended_execution_add_steps, appendedSampler_done]
  apply appendProgram_execution_decode
  simp [appendedSamplerBoundary]

end CountingMatroid.Bridge

abbrev solution := @CountingMatroid.Bridge.appendedSampler_then_program
