-- Prove2me | solution 1 for CountingMatroid.Bridge.setMembershipBitProgram_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T16:11:14.568281+00:00
-- url     : https://prove2.me/submissions/8e72dfcb-b1de-48cf-af80-8707bdd8edcc

import Definitions.Def_CountingMatroid_Bridge_SetMembershipBitProgram


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CountingMatroid.Bridge

open OAI.CommonBasesFPRAS

private theorem execution_add_steps {k s n : ℕ} (P : Program k s)
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

private theorem setBit_scan_cycle {n : ℕ} (value toggle : Bool) (next : Fin 12)
    (O : IndependenceOracle n) (bits : ℕ → Bool) (c : MachineConfig 2 11)
    (b : Bool) (tail scratch indexTail : List Bool)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = b :: tail)
    (h7 : c.registers 7 = true :: indexTail)
    (h8 : c.registers 8 = scratch) :
    let out := execution (membershipBitProgram value toggle next) O c bits 3
    out.control.val = 0 ∧ out.registers 6 = tail ∧
      out.registers 7 = indexTail ∧ out.registers 8 = b :: scratch ∧
      out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + 3 := by
  cases b <;>
    simp [execution, machineStep, membershipBitProgram, hc, ho, h6, h7, h8,
      Function.update]

/-- Scanning a set-bit preBits preserves its order on the vector stack and
stores the reversed preBits on scratch. -/
private theorem setMembershipBit_scan {n : ℕ} (value toggle : Bool) (next : Fin 12)
    (O : IndependenceOracle n) (bits : ℕ → Bool) (c : MachineConfig 2 11)
    (preBits : List Bool) (selected : Bool) (suffix base : List Bool)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = preBits ++ selected :: suffix)
    (h7 : c.registers 7 = List.replicate preBits.length true)
    (h8 : c.registers 8 = base) :
    let out := execution (membershipBitProgram value toggle next) O c bits
      (3 * preBits.length)
    out.control.val = 0 ∧ out.registers 6 = selected :: suffix ∧
      out.registers 7 = [] ∧ out.registers 8 = preBits.reverse ++ base ∧
      out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + 3 * preBits.length := by
  induction preBits generalizing bits c base with
  | nil =>
      simp only [execution, List.length_nil, Nat.mul_zero, List.replicate,
        List.reverse_nil, List.nil_append, hc, h6, h7, h8, ho]
      simp
  | cons b preBits ih =>
      have h6' : c.registers 6 = b :: (preBits ++ selected :: suffix) := by
        simpa [List.cons_append, List.append_assoc] using h6
      have h7' : c.registers 7 = true :: List.replicate preBits.length true := by
        simpa [List.length_cons, List.replicate_succ] using h7
      let c₁ := execution (membershipBitProgram value toggle next) O c bits 3
      have hcycle := setBit_scan_cycle value toggle next O bits c b
        (preBits ++ selected :: suffix) base
        (List.replicate preBits.length true) hc ho h6' h7' h8
      have hc₁ : c₁.control.val = 0 := by simpa [c₁] using hcycle.1
      have h6₁ : c₁.registers 6 = preBits ++ selected :: suffix := by
        simpa [c₁] using hcycle.2.1
      have h7₁ : c₁.registers 7 = List.replicate preBits.length true := by
        simpa [c₁] using hcycle.2.2.1
      have h8₁ : c₁.registers 8 = b :: base := by
        simpa [c₁, List.cons_append] using hcycle.2.2.2.1
      have hout₁ : c₁.output = none := by simpa [c₁] using hcycle.2.2.2.2.1
      have hrun : execution (membershipBitProgram value toggle next) O c bits
          (3 * (preBits.length + 1)) =
        execution (membershipBitProgram value toggle next) O c₁
          (fun t => bits (3 + t)) (3 * preBits.length) := by
        rw [show 3 * (preBits.length + 1) = 3 + 3 * preBits.length by omega,
          execution_add_steps]
      dsimp only
      simp only [List.length_cons]
      rw [hrun]
      have htail := ih (fun t => bits (3 + t)) c₁ (b :: base)
        hc₁ hout₁ h6₁ h7₁ h8₁
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact htail.1
      · exact htail.2.1
      · exact htail.2.2.1
      · simpa [List.reverse_cons, List.append_assoc] using htail.2.2.2.1
      · exact htail.2.2.2.2.1
      · calc
          _ = c₁.oracleCalls := htail.2.2.2.2.2.1
          _ = c.oracleCalls := by simpa [c₁] using hcycle.2.2.2.2.2.1
      · calc
          _ = c₁.bitOperations + 3 * preBits.length := htail.2.2.2.2.2.2
          _ = c.bitOperations + 3 * (preBits.length + 1) := by
            rw [show c₁.bitOperations = c.bitOperations + 3 by
              simpa [c₁] using hcycle.2.2.2.2.2.2]
            omega

/-- Replace the current head bit and enter scratch restoration. -/
private theorem setMembershipBit_select {n : ℕ} (value toggle : Bool) (next : Fin 12)
    (O : IndependenceOracle n) (bits : ℕ → Bool) (c : MachineConfig 2 11)
    (selected : Bool) (suffix saved : List Bool)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = selected :: suffix)
    (h7 : c.registers 7 = []) (h8 : c.registers 8 = saved) :
    let out := execution (membershipBitProgram value toggle next) O c bits 3
    out.control.val = 6 ∧ out.registers 6 = membershipBitResult value toggle selected :: suffix ∧
      out.registers 7 = [] ∧ out.registers 8 = saved ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls ∧ out.bitOperations = c.bitOperations + 3 := by
  cases selected <;> cases toggle <;>
    simp [execution, machineStep, membershipBitProgram, membershipBitResult, hc, ho, h6, h7, h8,
      Function.update]

/-- Restore the bits saved during the scan, then call the continuation. -/
private theorem setMembershipBit_restore {n : ℕ} (value toggle : Bool) (next : Fin 12)
    (O : IndependenceOracle n) (bits : ℕ → Bool) (c : MachineConfig 2 11)
    (saved target : List Bool) (hc : c.control.val = 6) (ho : c.output = none)
    (h6 : c.registers 6 = target) (h7 : c.registers 7 = [])
    (h8 : c.registers 8 = saved) :
    let out := execution (membershipBitProgram value toggle next) O c bits
      (2 * saved.length + 2)
    out.control = next ∧ out.registers 6 = saved.reverse ++ target ∧
      out.registers 7 = [] ∧ out.registers 8 = [] ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + (2 * saved.length + 2) := by
  induction saved generalizing bits c target with
  | nil =>
    simp [execution, machineStep, membershipBitProgram, hc, ho, h6, h7, h8]
  | cons b saved ih =>
      let c₁ := execution (membershipBitProgram value toggle next) O c bits 2
      have hcycle :
          c₁.control.val = 6 ∧ c₁.registers 6 = b :: target ∧
          c₁.registers 7 = [] ∧ c₁.registers 8 = saved ∧ c₁.output = none ∧
          c₁.oracleCalls = c.oracleCalls ∧ c₁.bitOperations = c.bitOperations + 2 := by
        cases b <;> simp [c₁, execution, machineStep, membershipBitProgram,
          hc, ho, h6, h7, h8, Function.update]
      have hrun : execution (membershipBitProgram value toggle next) O c bits
          (2 * (saved.length + 1) + 2) =
        execution (membershipBitProgram value toggle next) O c₁
          (fun t => bits (2 + t)) (2 * saved.length + 2) := by
        rw [show 2 * (saved.length + 1) + 2 = 2 + (2 * saved.length + 2) by omega,
          execution_add_steps]
      dsimp only
      simp only [List.length_cons]
      rw [hrun]
      have htail := ih (fun t => bits (2 + t)) c₁ (b :: target)
        hcycle.1 hcycle.2.2.2.2.1
        hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2.1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact htail.1
      · simpa [List.reverse_cons, List.append_assoc] using htail.2.1
      · exact htail.2.2.1
      · exact htail.2.2.2.1
      · exact htail.2.2.2.2.1
      · calc
          _ = c₁.oracleCalls := htail.2.2.2.2.2.1
          _ = c.oracleCalls := hcycle.2.2.2.2.2.1
      · calc
          _ = c₁.bitOperations + (2 * saved.length + 2) := htail.2.2.2.2.2.2
          _ = c.bitOperations + (2 * saved.length + 4) := by
            rw [hcycle.2.2.2.2.2.2]
            omega

/-- Updating a membership vector is a fixed machine subroutine. It uses unary
index `preBits.length`, overwrites one bit, restores the untouched preBits, and
returns to `next`. The instruction and charged-bit cost is exactly `5*i+5`. -/
theorem membershipBitProgram_correct {n : ℕ} (value toggle : Bool) (next : Fin 12)
    (O : IndependenceOracle n) (bits : ℕ → Bool) (c : MachineConfig 2 11)
    (preBits : List Bool) (old : Bool) (suffix : List Bool)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = preBits ++ old :: suffix)
    (h7 : c.registers 7 = List.replicate preBits.length true)
    (h8 : c.registers 8 = []) :
    let out := execution (membershipBitProgram value toggle next) O c bits
      (5 * preBits.length + 5)
    out.control = next ∧
      out.registers 6 = preBits ++ membershipBitResult value toggle old :: suffix ∧
      out.registers 7 = [] ∧ out.registers 8 = [] ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + (5 * preBits.length + 5) := by
  let scanned := execution (membershipBitProgram value toggle next) O c bits
    (3 * preBits.length)
  have hs := setMembershipBit_scan value toggle next O bits c preBits old suffix []
    hc ho h6 h7 h8
  have hcScan : scanned.control.val = 0 := by simpa [scanned] using hs.1
  have h6Scan : scanned.registers 6 = old :: suffix := by simpa [scanned] using hs.2.1
  have h7Scan : scanned.registers 7 = [] := by simpa [scanned] using hs.2.2.1
  have h8Scan : scanned.registers 8 = preBits.reverse := by
    simpa [scanned] using hs.2.2.2.1
  have hoScan : scanned.output = none := by simpa [scanned] using hs.2.2.2.2.1
  have hcallsScan : scanned.oracleCalls = c.oracleCalls := by
    simpa [scanned] using hs.2.2.2.2.2.1
  have hcostScan : scanned.bitOperations = c.bitOperations + 3 * preBits.length := by
    simpa [scanned] using hs.2.2.2.2.2.2
  let selected := execution (membershipBitProgram value toggle next) O
    scanned (fun t => bits (3 * preBits.length + t)) 3
  have hsel := setMembershipBit_select value toggle next O
    (fun t => bits (3 * preBits.length + t)) scanned old suffix preBits.reverse
    hcScan hoScan h6Scan h7Scan h8Scan
  have hcSelected : selected.control.val = 6 := by simpa [selected] using hsel.1
  have h6Selected : selected.registers 6 =
      membershipBitResult value toggle old :: suffix := by
    simpa [selected] using hsel.2.1
  have h7Selected : selected.registers 7 = [] := by simpa [selected] using hsel.2.2.1
  have h8Selected : selected.registers 8 = preBits.reverse := by
    simpa [selected] using hsel.2.2.2.1
  have hoSelected : selected.output = none := by
    simpa [selected] using hsel.2.2.2.2.1
  have hcallsSelected : selected.oracleCalls = c.oracleCalls := by
    calc
      _ = scanned.oracleCalls := by simpa [selected] using hsel.2.2.2.2.2.1
      _ = c.oracleCalls := hcallsScan
  have hcostSelected : selected.bitOperations = c.bitOperations + 3 * preBits.length + 3 := by
    calc
      _ = scanned.bitOperations + 3 := by simpa [selected] using hsel.2.2.2.2.2.2
      _ = c.bitOperations + 3 * preBits.length + 3 := by rw [hcostScan]
  have hrestore := setMembershipBit_restore value toggle next O
    (fun t => bits (3 * preBits.length + 3 + t)) selected preBits.reverse
      (membershipBitResult value toggle old :: suffix)
    hcSelected hoSelected h6Selected h7Selected h8Selected
  have hrestore' := hrestore
  simp only [List.length_reverse] at hrestore'
  have hpreBits : execution (membershipBitProgram value toggle next) O c bits
      (3 * preBits.length + 3) = selected := by
    rw [execution_add_steps]
  have hrun : execution (membershipBitProgram value toggle next) O c bits
      (5 * preBits.length + 5) =
    execution (membershipBitProgram value toggle next) O selected
      (fun t => bits (3 * preBits.length + 3 + t))
      (2 * preBits.length + 2) := by
    rw [show 5 * preBits.length + 5 =
      (3 * preBits.length + 3) + (2 * preBits.length + 2) by omega,
      execution_add_steps, hpreBits]
  dsimp only
  rw [hrun]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hrestore'.1
  · simpa [List.reverse_reverse, List.append_assoc] using hrestore'.2.1
  · exact hrestore'.2.2.1
  · exact hrestore'.2.2.2.1
  · exact hrestore'.2.2.2.2.1
  · calc
      _ = selected.oracleCalls := hrestore'.2.2.2.2.2.1
      _ = c.oracleCalls := hcallsSelected
  · calc
      _ = selected.bitOperations + (2 * preBits.length + 2) := hrestore'.2.2.2.2.2.2
      _ = c.bitOperations + (5 * preBits.length + 5) := by
        rw [hcostSelected]
        omega

/-- The set-bit interface is a specialization of the generic updater. -/
theorem setMembershipBitProgram_correct {n : ℕ} (value : Bool) (next : Fin 12)
    (O : IndependenceOracle n) (bits : ℕ → Bool) (c : MachineConfig 2 11)
    (preBits : List Bool) (old : Bool) (suffix : List Bool)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = preBits ++ old :: suffix)
    (h7 : c.registers 7 = List.replicate preBits.length true)
    (h8 : c.registers 8 = []) :
    let out := execution (setMembershipBitProgram value next) O c bits
      (5 * preBits.length + 5)
    out.control = next ∧ out.registers 6 = preBits ++ value :: suffix ∧
      out.registers 7 = [] ∧ out.registers 8 = [] ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + (5 * preBits.length + 5) := by
  simpa [setMembershipBitProgram, membershipBitResult] using
    (membershipBitProgram_correct value false next O bits c preBits old suffix
      hc ho h6 h7 h8)

end CountingMatroid.Bridge

open CountingMatroid.Bridge OAI.CommonBasesFPRAS

theorem solution {n : ℕ} (value : Bool) (next : Fin 12)
    (O : IndependenceOracle n) (bits : ℕ → Bool) (c : MachineConfig 2 11)
    (preBits : List Bool) (old : Bool) (suffix : List Bool)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = preBits ++ old :: suffix)
    (h7 : c.registers 7 = List.replicate preBits.length true)
    (h8 : c.registers 8 = []) :
    let out := execution (setMembershipBitProgram value next) O c bits
      (5 * preBits.length + 5)
    out.control = next ∧ out.registers 6 = preBits ++ value :: suffix ∧
      out.registers 7 = [] ∧ out.registers 8 = [] ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + (5 * preBits.length + 5) := by
  exact CountingMatroid.Bridge.setMembershipBitProgram_correct value next O bits c
    preBits old suffix hc ho h6 h7 h8

#print axioms solution
