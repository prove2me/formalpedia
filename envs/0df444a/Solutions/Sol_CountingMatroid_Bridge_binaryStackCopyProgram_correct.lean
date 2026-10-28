-- Prove2me | solution 1 for CountingMatroid.Bridge.binaryStackCopyProgram_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T23:03:13.557257+00:00
-- url     : https://prove2.me/submissions/f37a6823-3d9f-4fe0-8170-dd4cabd7fb1f

import Definitions.Def_CountingMatroidBridgeStackCopy

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS
open CountingMatroid.Bridge

private theorem execution_add {k s n : ℕ} (P : Program k s)
    (O : IndependenceOracle n) (c : MachineConfig k s) (bits : ℕ → Bool)
    (t d : ℕ) :
    execution P O c bits (t + d) =
      execution P O (execution P O c bits t) (fun j => bits (t + j)) d := by
  induction d with
  | zero => simp [execution]
  | succ d ih => rw [Nat.add_succ, execution, ih, execution]

private theorem binaryStackCopy_scan {n : ℕ}
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 5 8) (xs tmp saved : List Bool)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = xs) (h10 : c.registers 10 = saved)
    (h11 : c.registers 11 = tmp) :
    let out := execution binaryStackCopyProgram O c bits (2 * xs.length + 1)
    out.control.val = 2 ∧ out.registers 6 = [] ∧
      out.registers 10 = saved ∧ out.registers 11 = xs.reverse ++ tmp ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + (2 * xs.length + 1) := by
  induction xs generalizing c tmp saved bits with
  | nil =>
      dsimp only
      have hcontrol : c.control = ⟨0, by omega⟩ := Fin.ext hc
      have hstep : machineStep binaryStackCopyProgram O (bits 0) c =
          { c with control := 2, bitOperations := c.bitOperations + 1 } := by
        simp [machineStep, binaryStackCopyProgram, hcontrol, h6, ho]
      simp [execution, hstep, h6, h10, h11, ho]
  | cons b xs ih =>
      let c₁ := machineStep binaryStackCopyProgram O (bits 0) c
      let c₂ := machineStep binaryStackCopyProgram O (bits 1) c₁
      have hcontrol : c.control = ⟨0, by omega⟩ := Fin.ext hc
      have hstep₁ : c₁ =
          { c with
            registers := Function.update c.registers ⟨6, by omega⟩ xs
            control := (if b then 3 else 1)
            bitOperations := c.bitOperations + 1 } := by
        cases b <;> simp [c₁, machineStep, binaryStackCopyProgram, hcontrol, h6, ho]
      have hstep₂ : c₂ =
          { c₁ with
            registers := Function.update c₁.registers ⟨11, by omega⟩ (b :: tmp)
            control := 0
            bitOperations := c₁.bitOperations + 1 } := by
        cases b <;>
          simp [c₂, machineStep, binaryStackCopyProgram, hstep₁,
            Function.update_apply, Fin.ext_iff, ho, h11]
      have htwo : execution binaryStackCopyProgram O c bits 2 = c₂ := by
        simp [execution, c₁, c₂]
      have h6₂ : c₂.registers 6 = xs := by
        rw [hstep₂, hstep₁]
        simp [Function.update_apply, Fin.ext_iff]
      have h11₂ : c₂.registers 11 = b :: tmp := by
        rw [hstep₂]
        simp [Function.update_apply, Fin.ext_iff]
      have h10₂ : c₂.registers 10 = saved := by
        rw [hstep₂, hstep₁]
        simp [Function.update_apply, Fin.ext_iff, h10]
      have hc₂ : c₂.control.val = 0 := by simp [c₂, hstep₂]
      have ho₂ : c₂.output = none := by rw [hstep₂, hstep₁]; exact ho
      have hrec := ih (fun j => bits (2 + j)) c₂ (b :: tmp) saved hc₂ ho₂ h6₂ h10₂ h11₂
      have hsplit : 2 * (b :: xs).length + 1 = 2 + (2 * xs.length + 1) := by
        simp; omega
      dsimp only
      rw [hsplit, execution_add, htwo]
      rcases hrec with ⟨hcontrol₂, h6final, h10final, h11final, hout₂, hcalls₂, hcost₂⟩
      have hcallsConfig : c₂.oracleCalls = c.oracleCalls := by
        simp [c₂, hstep₂, c₁, hstep₁]
      have hcostConfig : c₂.bitOperations = c.bitOperations + 2 := by
        simp [c₂, hstep₂, c₁, hstep₁]
      refine ⟨hcontrol₂, h6final, h10final, ?_, hout₂, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using h11final
      · rw [hcallsConfig] at hcalls₂
        exact hcalls₂
      · rw [hcost₂, hcostConfig]
        omega

private theorem binaryStackCopy_restore {n : ℕ}
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 5 8) (xs ys zs : List Bool)
    (hc : c.control.val = 2) (ho : c.output = none)
    (h6 : c.registers 6 = ys) (h10 : c.registers 10 = zs)
    (h11 : c.registers 11 = xs) :
    let out := execution binaryStackCopyProgram O c bits (3 * xs.length + 1)
    out.control.val = 6 ∧ out.registers 6 = xs.reverse ++ ys ∧
      out.registers 10 = xs.reverse ++ zs ∧ out.registers 11 = [] ∧
      out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + (3 * xs.length + 1) := by
  induction xs generalizing c ys zs bits with
  | nil =>
      dsimp only
      have hcontrol : c.control = ⟨2, by omega⟩ := Fin.ext hc
      have hstep : machineStep binaryStackCopyProgram O (bits 0) c =
          { c with control := 6, bitOperations := c.bitOperations + 1 } := by
        simp [machineStep, binaryStackCopyProgram, hcontrol, h11, ho]
      simp [execution, hstep, h6, h10, h11, ho]
  | cons b xs ih =>
      let c₁ := machineStep binaryStackCopyProgram O (bits 0) c
      let c₂ := machineStep binaryStackCopyProgram O (bits 1) c₁
      let c₃ := machineStep binaryStackCopyProgram O (bits 2) c₂
      have hcontrol : c.control = ⟨2, by omega⟩ := Fin.ext hc
      have hpop : c₁ =
          { c with
            registers := Function.update c.registers ⟨11, by omega⟩ xs
            control := (if b then 5 else 4)
            bitOperations := c.bitOperations + 1 } := by
        cases b <;> simp [c₁, machineStep, binaryStackCopyProgram, hcontrol, h11, ho]
      have h10₁ : c₁.registers 10 = zs := by
        rw [hpop]
        simp [Function.update_apply, Fin.ext_iff, h10]
      have ho₁ : c₁.output = none := by rw [hpop]; exact ho
      have hpush₆ : c₂ =
          { c₁ with
            registers := Function.update c₁.registers ⟨6, by omega⟩ (b :: ys)
            control := (if b then 8 else 7)
            bitOperations := c₁.bitOperations + 1 } := by
        cases b <;> simp [c₂, machineStep, binaryStackCopyProgram, hpop, h6, ho]
      have hpush₁₀ : c₃ =
          { c₂ with
            registers := Function.update c₂.registers ⟨10, by omega⟩ (b :: zs)
            control := 2
            bitOperations := c₂.bitOperations + 1 } := by
        cases b <;> simp [c₃, machineStep, binaryStackCopyProgram, hpush₆, h10₁, ho₁]
      have hthree : execution binaryStackCopyProgram O c bits 3 = c₃ := by
        simp [execution, c₁, c₂, c₃]
      have h6₃ : c₃.registers 6 = b :: ys := by
        rw [hpush₁₀, hpush₆]
        simp [Function.update_apply, Fin.ext_iff]
      have h10₃ : c₃.registers 10 = b :: zs := by
        rw [hpush₁₀]
        simp [Function.update_apply, Fin.ext_iff]
      have h11₃ : c₃.registers 11 = xs := by
        rw [hpush₁₀, hpush₆, hpop]
        simp [Function.update_apply, Fin.ext_iff]
      have hc₃ : c₃.control.val = 2 := by simp [c₃, hpush₁₀]
      have ho₃ : c₃.output = none := by rw [hpush₁₀, hpush₆, hpop]; exact ho
      have hrec := ih (fun j => bits (3 + j)) c₃ (b :: ys) (b :: zs) hc₃ ho₃ h6₃ h10₃ h11₃
      have hsplit : 3 * (b :: xs).length + 1 = 3 + (3 * xs.length + 1) := by
        simp; omega
      dsimp only
      rw [hsplit, execution_add, hthree]
      rcases hrec with ⟨hcontrol₃, h6final, h10final, h11final,
        hout₃, hcalls₃, hcost₃⟩
      have hcallsConfig : c₃.oracleCalls = c.oracleCalls := by
        simp [c₃, hpush₁₀, hpush₆, c₂, hpop, c₁]
      have hcostConfig : c₃.bitOperations = c.bitOperations + 3 := by
        simp [c₃, hpush₁₀, hpush₆, c₂, hpop, c₁]
      refine ⟨hcontrol₃, ?_, ?_, h11final, hout₃, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using h6final
      · simpa [List.reverse_cons, List.append_assoc] using h10final
      · rw [hcallsConfig] at hcalls₃
        exact hcalls₃
      · rw [hcost₃, hcostConfig]
        omega

/-- Copy a finite bit stack in its original order, preserving the source. The
temporary register is empty on return; execution and bit-operation cost are
both exactly linear in the source length. -/
theorem solution {n : ℕ}
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 5 8) (xs ys : List Bool)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = xs) (h10 : c.registers 10 = ys)
    (h11 : c.registers 11 = []) :
    let out := execution binaryStackCopyProgram O c bits (5 * xs.length + 2)
    out.control.val = 6 ∧ out.registers 6 = xs ∧
      out.registers 10 = xs ++ ys ∧ out.registers 11 = [] ∧
      out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + (5 * xs.length + 2) := by
  let c₁ := execution binaryStackCopyProgram O c bits (2 * xs.length + 1)
  have hscan := binaryStackCopy_scan O bits c xs [] ys hc ho h6 h10 h11
  have hsplit : 5 * xs.length + 2 = (2 * xs.length + 1) + (3 * xs.length + 1) := by omega
  dsimp only
  rw [hsplit, execution_add]
  rcases hscan with ⟨hc₁, h6₁, h10scan, h11₁, ho₁, hcalls₁, hcost₁⟩
  have h6₁' : c₁.registers 6 = [] := h6₁
  have h10₁ : c₁.registers 10 = ys := h10scan
  have h11₁' : c₁.registers 11 = xs.reverse := by simpa using h11₁
  have hrestore := binaryStackCopy_restore O (fun j => bits (2 * xs.length + 1 + j))
    c₁ xs.reverse [] ys (by omega) ho₁ h6₁' h10₁ h11₁'
  have hrestore' := by simpa only [List.length_reverse] using hrestore
  dsimp only [c₁] at hrestore'
  rcases hrestore' with ⟨hc₂, h6₂, h10₂, h11₂, ho₂, hcalls₂, hcost₂⟩
  refine ⟨hc₂, ?_, ?_, h11₂, ho₂, ?_, ?_⟩
  · simpa using h6₂
  · simpa [List.reverse_reverse] using h10₂
  · rw [hcalls₁] at hcalls₂
    exact hcalls₂
  · rw [hcost₂, hcost₁]
    omega
