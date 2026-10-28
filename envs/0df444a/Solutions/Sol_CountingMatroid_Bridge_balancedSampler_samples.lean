-- Prove2me | solution 1 for CountingMatroid.Bridge.balancedSampler_samples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T04:02:09.501989+00:00
-- url     : https://prove2.me/submissions/113d8dbb-fae6-4dfc-8154-6e2a8530197e

import Definitions.Def_CountingMatroidBridgeBalancedSampler
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CountingMatroid.Bridge
open OAI.CommonBasesFPRAS

theorem execution_add_steps {k s n : ℕ} (P : Program k s) (O : IndependenceOracle n)
    (c : MachineConfig k s) (bits : ℕ → Bool) (a b : ℕ) :
    execution P O c bits (a + b) =
      execution P O (execution P O c bits a) (fun t => bits (a + t)) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
      change machineStep P O (bits (a + b)) (execution P O c bits (a + b)) = _
      rw [ih]
      rfl

theorem balancedSampler_cycle {n : ℕ} (O : IndependenceOracle n)
    (c : MachineConfig 2 4) (bits : ℕ → Bool) (b : Bool) (rest : List Bool)
    (hcontrol : c.control = 0) (houtput : c.output = none)
    (hcounter : c.registers 8 = b :: rest) :
    execution balancedSampler O c bits 3 =
      { c with
        registers := Function.update (Function.update c.registers 8 rest) 9
          (bits 1 :: c.registers 9)
        control := 0
        bitOperations := c.bitOperations + 3 } := by
  cases hbit : bits 1 <;>
    simp [execution, machineStep, balancedSampler, hcontrol, houtput, hcounter,
      hbit, Function.update, Nat.add_assoc]

theorem balancedSampler_prefix {n : ℕ} (O : IndependenceOracle n)
    (c : MachineConfig 2 4) (bits : ℕ → Bool) (K m : ℕ) (hm : m ≤ K) :
    execution balancedSampler O (samplingConfig c bits K 0) bits (3 * m) =
      samplingConfig c bits K m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hrem : K - m = (K - (m + 1)) + 1 := by omega
    rw [show 3 * (m + 1) = 3 * m + 3 by omega, execution_add_steps, ih (by omega)]
    rw [balancedSampler_cycle O _ _ false (List.replicate (K - (m + 1)) false)
      rfl rfl (by simp [samplingConfig, hrem, List.replicate_succ])]
    simp [samplingConfig, sampledStack, Function.update, Nat.mul_add, Nat.add_assoc]
    funext i
    by_cases h8 : i = 8 <;> by_cases h9 : i = 9 <;> simp_all [Function.update]

theorem balancedSampler_done {n : ℕ} (O : IndependenceOracle n)
    (c : MachineConfig 2 4) (bits : ℕ → Bool) (K : ℕ) :
    execution balancedSampler O (samplingConfig c bits K 0) bits (3 * K + 1) =
      { samplingConfig c bits K K with
        control := 4
        bitOperations := c.bitOperations + (3 * K + 1) } := by
  rw [execution, balancedSampler_prefix O c bits K K (by rfl)]
  simp [machineStep, balancedSampler, samplingConfig, Nat.add_assoc]

theorem sampledStack_eq_reverse_ofFn {K : ℕ} (bits : ℕ → Bool) :
    sampledStack bits K =
      (List.ofFn (fun i : Fin K => bits (3 * i.val + 1))).reverse := by
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [sampledStack, List.ofFn_succ']
      simp only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last]
      rw [List.reverse_concat']
      simpa [Nat.mul_add] using congrArg (fun xs => bits (3 * K + 1) :: xs) ih

theorem balancedSampler_samples {n : ℕ} (O : IndependenceOracle n)
    (c : MachineConfig 2 4) (bits : ℕ → Bool) (K : ℕ) :
    let out := execution balancedSampler O (samplingConfig c bits K 0) bits (3 * K + 1)
    out.control = 4 ∧ out.output = none ∧ out.registers 8 = [] ∧
    out.registers 9 =
      (List.ofFn (fun i : Fin K => bits ((samplingPositions K i).val))).reverse ++
        c.registers 9 ∧
    out.bitOperations = c.bitOperations + (3 * K + 1) := by
  dsimp only
  rw [balancedSampler_done]
  simp [samplingConfig, sampledStack_eq_reverse_ofFn, samplingPositions, Function.update]
  funext i
  change bits (3 * i.val + 1) = bits (3 * i.val + 1)
  rfl

end CountingMatroid.Bridge

abbrev solution := @CountingMatroid.Bridge.balancedSampler_samples
