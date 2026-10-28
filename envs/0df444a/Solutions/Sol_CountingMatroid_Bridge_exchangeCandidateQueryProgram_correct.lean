-- Prove2me | solution 1 for CountingMatroid.Bridge.exchangeCandidateQueryProgram_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:08:17.992251+00:00
-- url     : https://prove2.me/submissions/0cbbd268-758b-43f5-9c9f-4d50f72efc0a

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_ExchangeCandidateQueryProgram
import Theorems.Thm_CountingMatroid_Bridge_setMembershipBitProgram_finset_correct

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid.Bridge OAI.CommonBasesFPRAS
open scoped Classical

private def remapInstruction {k a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) :
    Instruction k a → Instruction k b
  | .push i bit next => .push i bit (f next)
  | .pop i empty zero one => .pop i (f empty) (f zero) (f one)
  | .coin zero one => .coin (f zero) (f one)
  | .query which i no yes => .query which i (f no) (f yes)
  | .halt => .halt

private def remapConfig {k a b : ℕ} (f : Fin (a + 1) → Fin (b + 1))
    (c : MachineConfig k a) : MachineConfig k b where
  registers := c.registers
  control := f c.control
  output := c.output
  oracleCalls := c.oracleCalls
  bitOperations := c.bitOperations

private def exchangeFirstMap (q : Fin 12) : Fin 28 := ⟨q.val, by omega⟩

private def exchangeSecondMap (q : Fin 12) : Fin 28 :=
  if h11 : q.val = 11 then ⟨27, by omega⟩
  else if h10 : q.val = 10 then ⟨16, by omega⟩
  else ⟨q.val + 17, by have hlt := q.isLt; omega⟩

private theorem exchangeFirstState_eq_map (q : Fin 12) :
    exchangeFirstState q = exchangeFirstMap q := by
  apply Fin.ext
  by_cases h : q.val = 11
  · simp [exchangeFirstState, exchangeFirstMap, h]
  · simp [exchangeFirstState, exchangeFirstMap, h]

private theorem exchangeSecondState_eq_map (q : Fin 12) :
    exchangeSecondState q = exchangeSecondMap q := by
  apply Fin.ext
  by_cases h11 : q.val = 11
  · simp [exchangeSecondState, exchangeSecondMap, h11]
  · by_cases h10 : q.val = 10
    · simp [exchangeSecondState, exchangeSecondMap, h11, h10]
    · have hlt : q.val < 10 := by omega
      simp [exchangeSecondState, exchangeSecondMap, h11, h10]

private theorem exchangeFirstInstruction_eq_remap (ins : Instruction 2 11) :
    exchangeFirstInstruction ins = remapInstruction exchangeFirstMap ins := by
  cases ins <;> simp [exchangeFirstInstruction, remapInstruction,
    exchangeFirstState_eq_map]

private theorem exchangeSecondInstruction_eq_remap (ins : Instruction 2 11) :
    exchangeSecondInstruction ins = remapInstruction exchangeSecondMap ins := by
  cases ins <;> simp [exchangeSecondInstruction, remapInstruction,
    exchangeSecondState_eq_map]

private theorem machineStep_remap {k a b n : ℕ}
    (P : Program k a) (Q : Program k b) (O : IndependenceOracle n)
    (bit : Bool) (c : MachineConfig k a)
    (f : Fin (a + 1) → Fin (b + 1))
    (hprogram : Q (f c.control) = remapInstruction f (P c.control)) :
    remapConfig f (machineStep P O bit c) =
      machineStep Q O bit (remapConfig f c) := by
  cases c with
  | mk regs control out calls ops =>
    cases out with
    | some value => rfl
    | none =>
      cases hinst : P control with
      | push i bit next =>
          simp [machineStep, remapConfig, remapInstruction, hinst, hprogram]
      | pop i empty zero one =>
          cases hstack : regs i with
          | nil => simp [machineStep, remapConfig, remapInstruction, hinst, hprogram, hstack]
          | cons bit rest =>
              cases bit <;>
                simp [machineStep, remapConfig, remapInstruction, hinst, hprogram, hstack]
      | coin zero one =>
          cases bit <;>
            simp [machineStep, remapConfig, remapInstruction, hinst, hprogram]
      | query which i no yes =>
          by_cases hlen : (regs i).length = n
          · have hbits : (fun j : Fin n => (regs i)[j.val]?.getD false) =
                (fun j => (regs i)[j.val]) := by
              funext j
              simp [List.getElem?_eq_getElem (by rw [hlen]; exact j.isLt)]
            by_cases hquery : O which (fun j : Fin n => (regs i)[j.val]) = true
            · simp [machineStep, remapConfig, remapInstruction, hinst, hprogram, hlen, hbits, hquery]
            · simp [machineStep, remapConfig, remapInstruction, hinst, hprogram, hlen, hbits, hquery]
          · simp [machineStep, remapConfig, remapInstruction, hinst, hprogram, hlen]
      | halt => simp [machineStep, remapConfig, remapInstruction, hinst, hprogram]

private theorem execution_output_some_add_steps {k s n : ℕ}
    (P : Program k s) (O : IndependenceOracle n) (c : MachineConfig k s)
    (bits : ℕ → Bool) (t d : ℕ)
    (h : (execution P O c bits t).output.isSome) :
    (execution P O c bits (t + d)).output.isSome := by
  induction d with
  | zero => simpa using h
  | succ d ih =>
      rw [Nat.add_succ]
      simp [execution, ih, machineStep]

private theorem execution_remap_before_halt {k a b n : ℕ}
    (P : Program k a) (Q : Program k b) (O : IndependenceOracle n)
    (c : MachineConfig k a) (bits : ℕ → Bool) (t : ℕ)
    (f : Fin (a + 1) → Fin (b + 1)) (haltState : Fin (a + 1))
    (hprogram : ∀ q, q ≠ haltState →
      Q (f q) = remapInstruction f (P q))
    (hhalt : P haltState = .halt)
    (hfinal : (execution P O c bits t).output = none) :
    remapConfig f (execution P O c bits t) =
      execution Q O (remapConfig f c) bits t := by
  have hno : ∀ m, m < t → (execution P O c bits m).control ≠ haltState := by
    intro m hmt hcontrol
    let cm := execution P O c bits m
    have hnext : (machineStep P O (bits m) cm).output.isSome := by
      by_cases hsome : cm.output.isSome
      · simp [machineStep, hsome]
      · have hcm : cm.control = haltState := by simpa [cm] using hcontrol
        simp [machineStep, cm, hsome, hcm, hhalt]
    have htail := execution_output_some_add_steps P O c bits (m + 1)
      (t - (m + 1)) (by simpa [cm, execution] using hnext)
    have hindex : m + 1 + (t - (m + 1)) = t := by omega
    rw [hindex, hfinal] at htail
    simpa using htail
  have hrun : ∀ m, m ≤ t →
      remapConfig f (execution P O c bits m) =
        execution Q O (remapConfig f c) bits m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hmt
      have hprev := ih (by omega)
      have hcontrol := hno m (by omega)
      change remapConfig f
          (machineStep P O (bits m) (execution P O c bits m)) =
        machineStep Q O (bits m) (execution Q O (remapConfig f c) bits m)
      rw [← hprev]
      exact machineStep_remap P Q O (bits m) (execution P O c bits m) f
        (hprogram _ hcontrol)
  exact hrun t le_rfl

private theorem execution_add {k s n : ℕ} (P : Program k s)
    (O : IndependenceOracle n) (c : MachineConfig k s) (bits : ℕ → Bool)
    (t d : ℕ) :
    execution P O c bits (t + d) =
      execution P O (execution P O c bits t) (fun j => bits (t + j)) d := by
  induction d with
  | zero => simp [execution]
  | succ d ih =>
      rw [Nat.add_succ, execution, ih, execution]

private theorem replicate_true_move (v : ℕ) (pre : List Bool) :
    List.replicate v true ++ true :: pre =
      true :: (List.replicate v true ++ pre) := by
  induction v with
  | zero => rfl
  | succ v ih =>
      simp only [List.replicate_succ, List.cons_append]
      congr 1

private theorem copyUnaryIndex_loop {n : ℕ} (which : Bool)
    (O : IndependenceOracle n) (c : MachineConfig 2 27)
    (bits : ℕ → Bool) (pre : List Bool) (v : ℕ)
    (hc : c.control.val = 11 ∨ c.control.val = 13)
    (h6 : c.registers 6 = c.registers 6)
    (h7 : c.registers 7 = pre) (h8 : c.registers 8 = [])
    (h9 : c.registers 9 = List.replicate v true) (ho : c.output = none) :
    let out := execution (exchangeCandidateQueryProgram which) O c bits (2 * v + 1)
    out.control.val = 14 ∧ out.registers 6 = c.registers 6 ∧
      out.registers 7 = List.replicate v true ++ pre ∧
      out.registers 8 = [] ∧ out.registers 9 = [] ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + (2 * v + 1) := by
  induction v generalizing c pre bits with
  | zero =>
      have hstep : machineStep (exchangeCandidateQueryProgram which) O (bits 0) c =
          { c with
            control := ⟨14, by omega⟩
            bitOperations := c.bitOperations + 1 } := by
        rcases hc with h | h
        · have hcontrol : c.control = ⟨11, by omega⟩ := Fin.ext h
          simp [machineStep, exchangeCandidateQueryProgram, hcontrol, h9, ho]
        · have hcontrol : c.control = ⟨13, by omega⟩ := Fin.ext h
          simp [machineStep, exchangeCandidateQueryProgram, hcontrol, h9, ho]
      dsimp only
      norm_num [execution, hstep, h6, h7, h8, h9, ho, List.replicate]
  | succ v ih =>
      let c₁ := machineStep (exchangeCandidateQueryProgram which) O (bits 0) c
      let c₂ := machineStep (exchangeCandidateQueryProgram which) O (bits 1) c₁
      have hstep₁ : c₁ =
          { c with
            registers := Function.update c.registers ⟨9, by omega⟩
              (List.replicate v true)
            control := ⟨12, by omega⟩
            bitOperations := c.bitOperations + 1 } := by
        rcases hc with h | h
        · have hcontrol : c.control = ⟨11, by omega⟩ := Fin.ext h
          simp [c₁, machineStep, exchangeCandidateQueryProgram, hcontrol, h9,
            List.replicate_succ, ho]
        · have hcontrol : c.control = ⟨13, by omega⟩ := Fin.ext h
          simp [c₁, machineStep, exchangeCandidateQueryProgram, hcontrol, h9,
            List.replicate_succ, ho]
      have hstep₂ : c₂ =
          { c₁ with
            registers := Function.update c₁.registers ⟨7, by omega⟩
              (true :: c₁.registers ⟨7, by omega⟩)
            control := ⟨13, by omega⟩
            bitOperations := c₁.bitOperations + 1 } := by
        have hcontrol : c₁.control = ⟨12, by omega⟩ := by rw [hstep₁]
        have ho₁ : c₁.output = none := by rw [hstep₁]; exact ho
        simp [c₂, machineStep, exchangeCandidateQueryProgram, hcontrol, ho₁]
      have htwo : execution (exchangeCandidateQueryProgram which) O c bits 2 = c₂ := by
        simp [execution, c₁, c₂]
      have hc₂ : c₂.control.val = 13 := by rw [hstep₂]
      have h7₂ : c₂.registers 7 = true :: pre := by
        rw [hstep₂, hstep₁]
        simp [h7]
      have h8₂ : c₂.registers 8 = [] := by rw [hstep₂, hstep₁]; exact h8
      have h9₂ : c₂.registers 9 = List.replicate v true := by
        rw [hstep₂, hstep₁]
        simp [h9]
      have h6₂ : c₂.registers 6 = c.registers 6 := by
        rw [hstep₂, hstep₁]
        simp [Function.update_apply, Fin.ext_iff]
      have ho₂ : c₂.output = none := by rw [hstep₂, hstep₁]; exact ho
      have hcost₂ : c₂.bitOperations = c.bitOperations + 2 := by
        rw [hstep₂, hstep₁]
      have hcalls₂ : c₂.oracleCalls = c.oracleCalls := by
        rw [hstep₂, hstep₁]
      have hrec := ih c₂ (fun j => bits (2 + j)) (true :: pre)
        (Or.inr hc₂) rfl h7₂ h8₂ h9₂ ho₂
      have hsplit :
          execution (exchangeCandidateQueryProgram which) O c bits
            (2 * (v + 1) + 1) =
          execution (exchangeCandidateQueryProgram which) O c₂ (fun j => bits (2 + j)) (2 * v + 1) := by
        have htime : 2 * (v + 1) + 1 = 2 + (2 * v + 1) := by omega
        rw [htime, execution_add, htwo]
      dsimp only
      rw [hsplit]
      rcases hrec with ⟨hcFinal, h6Final, h7Final, h8Final, h9Final, hoFinal,
        hcallsFinal, hcostFinal⟩
      refine ⟨hcFinal, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact h6Final.trans h6₂
      · rw [replicate_true_move] at h7Final
        exact h7Final
      · exact h8Final
      · exact h9Final
      · exact hoFinal
      · rw [hcalls₂] at hcallsFinal
        exact hcallsFinal
      · rw [hcost₂] at hcostFinal
        omega

private theorem exchangeFirstProgram_remap (which : Bool) (q : Fin 12)
    (hq : q.val ≠ 11) :
    exchangeCandidateQueryProgram which (exchangeFirstMap q) =
      remapInstruction exchangeFirstMap
        (setMembershipBitProgram false ⟨11, by omega⟩ q) := by
  have hlt : q.val < 11 := by have := q.isLt; omega
  simp [exchangeCandidateQueryProgram, exchangeFirstMap, hlt,
    exchangeFirstInstruction_eq_remap]

private theorem exchangeSecondProgram_remap (which : Bool) (q : Fin 12)
    (hq : q.val ≠ 11) :
    exchangeCandidateQueryProgram which (exchangeSecondMap q) =
      remapInstruction exchangeSecondMap
        (setMembershipBitProgram true ⟨11, by omega⟩ q) := by
  by_cases h10 : q.val = 10
  · have hf : exchangeSecondMap q = ⟨16, by omega⟩ := by
      apply Fin.ext
      simp [exchangeSecondMap, hq, h10]
    have hq10 : q = ⟨10, by omega⟩ := Fin.ext h10
    rw [hq10]
    simp [exchangeSecondMap, exchangeCandidateQueryProgram,
      exchangeSecondInstruction_eq_remap]
  · have hlt : q.val < 10 := by have := q.isLt; omega
    have hf : exchangeSecondMap q = ⟨q.val + 17, by omega⟩ := by
      apply Fin.ext
      simp [exchangeSecondMap, hq, h10]
    rw [hf]
    have h17 : 17 ≤ q.val + 17 := by omega
    have h27 : q.val + 17 < 27 := by omega
    have hnot : ¬(q.val + 17 < 11) := by omega
    have hneq : q.val + 17 ≠ 10 := by omega
    simp [exchangeCandidateQueryProgram, h10, h17, h27, hnot, hneq,
      exchangeSecondInstruction_eq_remap]

private theorem update_register9 (regs : Fin 10 → List Bool) (i : Fin 10)
    (xs : List Bool) (hi : i ≠ ⟨9, by omega⟩) :
    (Function.update regs i xs) ⟨9, by omega⟩ = regs ⟨9, by omega⟩ := by
  apply Function.update_of_ne
  exact hi.symm

private theorem setter_machineStep_register9 {n : ℕ} (value : Bool) (next : Fin 12)
    (O : IndependenceOracle n) (bits : Bool) (c : MachineConfig 2 11) :
    (machineStep (setMembershipBitProgram value next) O bits c).registers 9 =
      c.registers 9 := by
  cases c with
  | mk regs control out calls ops =>
    cases out with
    | some value => rfl
    | none =>
      fin_cases control <;>
        simp [machineStep, setMembershipBitProgram, membershipBitProgram] <;>
        split <;> simp [Function.update_apply, Fin.ext_iff]

private theorem setter_execution_register9 {n : ℕ} (value : Bool) (next : Fin 12)
    (O : IndependenceOracle n) (c : MachineConfig 2 11) (bits : ℕ → Bool) :
    ∀ t, (execution (setMembershipBitProgram value next) O c bits t).registers 9 =
      c.registers 9 := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      change (machineStep (setMembershipBitProgram value next) O (bits t)
        (execution (setMembershipBitProgram value next) O c bits t)).registers 9 = _
      rw [setter_machineStep_register9]
      exact ih

private theorem exchangeCandidateQueryProgram_firstUpdate {n : ℕ}
    (which : Bool) (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 27) (I : Finset (Fin n)) (u : Fin n)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = finsetMembershipBits I)
    (h7 : c.registers 7 = List.replicate u.val true)
    (h8 : c.registers 8 = []) :
    let out := execution (exchangeCandidateQueryProgram which) O c bits (5 * u.val + 5)
    out.control.val = 11 ∧
      out.registers 6 = finsetMembershipBits (I.erase u) ∧
      out.registers 7 = [] ∧ out.registers 8 = [] ∧
      out.registers 9 = c.registers 9 ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + (5 * u.val + 5) := by
  let small : MachineConfig 2 11 := {
    registers := c.registers
    control := ⟨0, by omega⟩
    output := c.output
    oracleCalls := c.oracleCalls
    bitOperations := c.bitOperations
  }
  have hsmallControl : small.control.val = 0 := by rfl
  have hset := setMembershipBitProgram_finset_correct false
    ⟨11, by omega⟩ O bits small I u hsmallControl ho h6 h7 h8
  rcases hset with ⟨hsc, hs6, hs7, hs8, hso, hscalls, hscost⟩
  have hstart : remapConfig exchangeFirstMap small = c := by
    cases c with
    | mk regs control out calls ops =>
      have hcontrol : control.val = 0 := hc
      have hcontrolFin : control = ⟨0, by omega⟩ := Fin.ext hcontrol
      simp [small, remapConfig, exchangeFirstMap, hcontrolFin]
  have hprog : ∀ q : Fin 12, q ≠ (⟨11, by omega⟩ : Fin 12) →
      exchangeCandidateQueryProgram which (exchangeFirstMap q) =
        remapInstruction exchangeFirstMap
          (setMembershipBitProgram false ⟨11, by omega⟩ q) := by
    intro q hq
    exact exchangeFirstProgram_remap which q (by
      intro h
      apply hq
      exact Fin.ext h)
  have hhalt : setMembershipBitProgram false ⟨11, by omega⟩
      ⟨11, by omega⟩ = .halt := by
    simp [setMembershipBitProgram, membershipBitProgram]
  have hsim := execution_remap_before_halt
      (setMembershipBitProgram false ⟨11, by omega⟩)
      (exchangeCandidateQueryProgram which) O small bits (5 * u.val + 5)
      exchangeFirstMap ⟨11, by omega⟩ hprog hhalt hso
  have hsim' : remapConfig exchangeFirstMap
      (execution (setMembershipBitProgram false ⟨11, by omega⟩) O small bits
        (5 * u.val + 5)) =
      execution (exchangeCandidateQueryProgram which) O c bits (5 * u.val + 5) := by
    simpa [hstart] using hsim
  dsimp only
  rw [← hsim']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [remapConfig, exchangeFirstMap] using congrArg Fin.val hsc
  · simpa [remapConfig] using hs6
  · simpa [remapConfig] using hs7
  · simpa [remapConfig] using hs8
  · simpa [remapConfig] using setter_execution_register9 false ⟨11, by omega⟩ O
      small bits (5 * u.val + 5)
  · exact hso
  · simpa [remapConfig, small] using hscalls
  · simpa [remapConfig, small] using hscost

private theorem exchangeCandidateQueryProgram_twoUpdates {n : ℕ}
    (which : Bool) (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 27) (I : Finset (Fin n)) (u v : Fin n)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = finsetMembershipBits I)
    (h7 : c.registers 7 = List.replicate u.val true)
    (h8 : c.registers 8 = [])
    (h9 : c.registers 9 = List.replicate v.val true) :
    let out := execution (exchangeCandidateQueryProgram which) O c bits
      (5 * u.val + 7 * v.val + 12)
    out.control.val = 27 ∧
      out.registers 6 = finsetMembershipBits (insert v (I.erase u)) ∧
      out.registers 7 = [] ∧ out.registers 8 = [] ∧ out.registers 9 = [] ∧
      out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + (5 * u.val + 7 * v.val + 12) := by
  let t₁ := 5 * u.val + 5
  let tCopy := 2 * v.val + 2
  let t₂ := 5 * v.val + 5
  let P₂ := setMembershipBitProgram true (⟨11, by omega⟩ : Fin 12)
  let c₁ := execution (exchangeCandidateQueryProgram which) O c bits t₁
  have hfirst := exchangeCandidateQueryProgram_firstUpdate which O bits c I u hc ho h6 h7 h8
  rcases hfirst with ⟨hc₁, h16, h17, h18, h19, ho₁, hcalls₁, hcost₁⟩
  have hc₁' : c₁.control.val = 11 := by simpa [c₁, t₁] using hc₁
  have h16' : c₁.registers 6 = finsetMembershipBits (I.erase u) := by
    simpa [c₁, t₁] using h16
  have h17' : c₁.registers 7 = [] := by simpa [c₁, t₁] using h17
  have h18' : c₁.registers 8 = [] := by simpa [c₁, t₁] using h18
  have h19' : c₁.registers 9 = List.replicate v.val true := by
    simpa [c₁, t₁, h9] using h19
  have ho₁' : c₁.output = none := by simpa [c₁, t₁] using ho₁
  have hcalls₁' : c₁.oracleCalls = c.oracleCalls := by
    simpa [c₁, t₁] using hcalls₁
  have hcost₁' : c₁.bitOperations = c.bitOperations + t₁ := by
    simpa [c₁, t₁] using hcost₁
  let copyBits : ℕ → Bool := fun j => bits (t₁ + j)
  let c₂ := execution (exchangeCandidateQueryProgram which) O c₁ copyBits
    (2 * v.val + 1)
  have hcopy := copyUnaryIndex_loop which O c₁ copyBits [] v.val
    (Or.inl hc₁') rfl h17' h18' h19' ho₁'
  rcases hcopy with ⟨hc₂, h6₂, h27₂, h28₂, h29₂, ho₂, hcalls₂, hcost₂⟩
  have hc₂' : c₂.control.val = 14 := by simpa [c₂] using hc₂
  have h27₂' : c₂.registers 7 = List.replicate v.val true := by
    simpa [c₂] using h27₂
  have h28₂' : c₂.registers 8 = [] := by simpa [c₂] using h28₂
  have h29₂' : c₂.registers 9 = [] := by simpa [c₂] using h29₂
  have ho₂' : c₂.output = none := by simpa [c₂] using ho₂
  have hcalls₂' : c₂.oracleCalls = c₁.oracleCalls := by simpa [c₂] using hcalls₂
  have hcost₂' : c₂.bitOperations = c₁.bitOperations + (2 * v.val + 1) := by
    simpa [c₂] using hcost₂
  let c₃ := machineStep (exchangeCandidateQueryProgram which) O
    (copyBits (2 * v.val + 1)) c₂
  have hjump : c₃ = { c₂ with
      control := ⟨17, by omega⟩
      bitOperations := c₂.bitOperations + 1 } := by
    have hcontrol : c₂.control = ⟨14, by omega⟩ := Fin.ext hc₂'
    simp [c₃, machineStep, exchangeCandidateQueryProgram, hcontrol, h28₂', ho₂']
  have hcopyRun : execution (exchangeCandidateQueryProgram which) O c₁ copyBits tCopy = c₃ := by
    dsimp [tCopy, c₃, c₂]
    rw [show 2 * v.val + 2 = (2 * v.val + 1) + 1 by omega, execution]
  have hrunCopy : execution (exchangeCandidateQueryProgram which) O c bits
      (t₁ + tCopy) = c₃ := by
    calc
      execution (exchangeCandidateQueryProgram which) O c bits (t₁ + tCopy) =
          execution (exchangeCandidateQueryProgram which) O c₁ copyBits tCopy := by
            rw [execution_add]
      _ = c₃ := hcopyRun
  have hc₃ : c₃.control.val = 17 := by rw [hjump]
  have h63 : c₃.registers 6 = finsetMembershipBits (I.erase u) := by
    rw [hjump]
    simpa using h6₂.trans h16'
  have h73 : c₃.registers 7 = List.replicate v.val true := by
    rw [hjump]
    exact h27₂'
  have h83 : c₃.registers 8 = [] := by rw [hjump]; exact h28₂'
  have h93 : c₃.registers 9 = [] := by rw [hjump]; exact h29₂'
  have ho₃ : c₃.output = none := by rw [hjump]; exact ho₂'
  have hcalls₃ : c₃.oracleCalls = c.oracleCalls := by
    rw [hjump, hcalls₂', hcalls₁']
  have hcost₃ : c₃.bitOperations = c.bitOperations + (t₁ + tCopy) := by
    rw [hjump, hcost₂', hcost₁']
    dsimp [tCopy]
    omega
  let small₂ : MachineConfig 2 11 := {
    registers := c₃.registers
    control := ⟨0, by omega⟩
    output := c₃.output
    oracleCalls := c₃.oracleCalls
    bitOperations := c₃.bitOperations
  }
  have hstart₂ : remapConfig exchangeSecondMap small₂ = c₃ := by
    have hregs : c₃.registers = c₂.registers := by
      simpa using congrArg MachineConfig.registers hjump
    have hout : c₃.output = c₂.output := by
      simpa using congrArg MachineConfig.output hjump
    have hcalls : c₃.oracleCalls = c₂.oracleCalls := by
      simpa using congrArg MachineConfig.oracleCalls hjump
    have hops : c₃.bitOperations = c₂.bitOperations + 1 := by
      simpa using congrArg MachineConfig.bitOperations hjump
    rw [hjump]
    simp only [remapConfig, small₂, MachineConfig.mk.injEq]
    refine ⟨hregs, ?_, hout, hcalls, hops⟩
    apply Fin.ext
    simp [exchangeSecondMap]
  have hset₂ := setMembershipBitProgram_finset_correct true
    ⟨11, by omega⟩ O (fun j => bits (t₁ + tCopy + j)) small₂
    (I.erase u) v (by rfl) ho₃ h63 h73 h83
  rcases hset₂ with ⟨hs₂c, hs₂6, hs₂7, hs₂8, hs₂o, hs₂calls, hs₂cost⟩
  have hprog₂ : ∀ q : Fin 12, q ≠ (⟨11, by omega⟩ : Fin 12) →
      exchangeCandidateQueryProgram which (exchangeSecondMap q) =
        remapInstruction exchangeSecondMap (P₂ q) := by
    intro q hq
    exact exchangeSecondProgram_remap which q (by
      intro h
      apply hq
      exact Fin.ext h)
  have hhalt₂ : P₂ ⟨11, by omega⟩ = .halt := by
    simp [P₂, setMembershipBitProgram, membershipBitProgram]
  have hsim₂ := execution_remap_before_halt P₂
      (exchangeCandidateQueryProgram which) O small₂ (fun j => bits (t₁ + tCopy + j)) t₂
      exchangeSecondMap ⟨11, by omega⟩ hprog₂ hhalt₂ hs₂o
  have hsim₂' : remapConfig exchangeSecondMap
      (execution P₂ O small₂ (fun j => bits (t₁ + tCopy + j)) t₂) =
      execution (exchangeCandidateQueryProgram which) O c₃
        (fun j => bits (t₁ + tCopy + j)) t₂ := by
    simpa [hstart₂] using hsim₂
  have hfull : execution (exchangeCandidateQueryProgram which) O c bits
      (t₁ + tCopy + t₂) =
      remapConfig exchangeSecondMap
        (execution P₂ O small₂ (fun j => bits (t₁ + tCopy + j)) t₂) := by
    rw [execution_add, hrunCopy]
    exact hsim₂'.symm
  dsimp only
  rw [show 5 * u.val + 7 * v.val + 12 = t₁ + tCopy + t₂ by
    dsimp [t₁, tCopy, t₂]; omega, hfull]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (exchangeSecondMap
      (execution P₂ O small₂ (fun j => bits (t₁ + tCopy + j)) t₂).control).val = 27
    rw [hs₂c]
    simp [exchangeSecondMap]
  · simpa [remapConfig, P₂, t₂] using hs₂6
  · simpa [remapConfig, P₂, t₂] using hs₂7
  · simpa [remapConfig, P₂, t₂] using hs₂8
  · simpa [remapConfig, small₂, P₂, t₂, h93] using
      setter_execution_register9 true ⟨11, by omega⟩ O
        small₂ (fun j => bits (t₁ + tCopy + j)) t₂
  · simpa [remapConfig, P₂, t₂] using hs₂o
  · simpa [remapConfig, small₂, P₂, t₂, hcalls₃] using hs₂calls
  · change (execution P₂ O small₂ (fun j => bits (t₁ + tCopy + j)) t₂).bitOperations =
      c.bitOperations + (t₁ + tCopy + t₂)
    rw [hs₂cost]
    dsimp [small₂]
    rw [hcost₃]
    omega

theorem solution {n : ℕ}
    (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n)) (u v : Fin n)
    (which : Bool) (O : IndependenceOracle n)
    (hExact : ExactOracles M₁ M₂ O) (bits : ℕ → Bool)
    (c : MachineConfig 2 27)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = finsetMembershipBits I)
    (h7 : c.registers 7 = List.replicate u.val true)
    (h8 : c.registers 8 = []) (h9 : c.registers 9 = List.replicate v.val true) :
    let S := insert v (I.erase u)
    let t := 5 * u.val + 7 * v.val + 12
    let out := execution (exchangeCandidateQueryProgram which) O c bits (t + 1)
    out.control.val = (if (if which then M₂ else M₁).Indep (S : Set (Fin n)) then 11 else 10) ∧
      out.registers 6 = finsetMembershipBits S ∧ out.registers 7 = [] ∧
      out.registers 8 = [] ∧ out.registers 9 = [] ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls + 1 ∧
      out.bitOperations = c.bitOperations + t + (2 * n + 1) := by
  let S : Finset (Fin n) := insert v (I.erase u)
  let t := 5 * u.val + 7 * v.val + 12
  let c₁ := execution (exchangeCandidateQueryProgram which) O c bits t
  have hrun := exchangeCandidateQueryProgram_twoUpdates which O bits c I u v
    hc ho h6 h7 h8 h9
  have hcontrol : c₁.control.val = 27 := by simpa [c₁, t] using hrun.1
  have hregs6 : c₁.registers 6 = finsetMembershipBits S := by
    simpa [c₁, t, S] using hrun.2.1
  have hregs7 : c₁.registers 7 = [] := by simpa [c₁, t] using hrun.2.2.1
  have hregs8 : c₁.registers 8 = [] := by simpa [c₁, t] using hrun.2.2.2.1
  have hregs9 : c₁.registers 9 = [] := by simpa [c₁, t] using hrun.2.2.2.2.1
  have hout : c₁.output = none := by simpa [c₁, t] using hrun.2.2.2.2.2.1
  have hcalls : c₁.oracleCalls = c.oracleCalls := by simpa [c₁, t] using hrun.2.2.2.2.2.2.1
  have hcost : c₁.bitOperations = c.bitOperations + t := by simpa [c₁, t] using hrun.2.2.2.2.2.2.2
  let q : Fin n → Bool := fun j => decide (j ∈ S)
  have hlen : (finsetMembershipBits S).length = n := by simp [finsetMembershipBits]
  have hsetEq : {j : Fin n | q j = true} = (S : Set (Fin n)) := by
    ext j
    simp [q]
  have hSSet : (S : Set (Fin n)) = insert v ((I : Set (Fin n)) \ {u}) := by
    ext j
    simp [S]
  have hIndepSet : (if which then M₂ else M₁).Indep (S : Set (Fin n)) =
      (if which then M₂ else M₁).Indep (insert v ((I : Set (Fin n)) \ {u})) :=
    congrArg (fun X : Set (Fin n) => (if which then M₂ else M₁).Indep X) hSSet
  have hExactQ := hExact which q
  have hOracle : O which q = decide ((if which then M₂ else M₁).Indep (S : Set (Fin n))) := by
    by_cases hi : (if which then M₂ else M₁).Indep (S : Set (Fin n))
    · have htrue : O which q = true := hExactQ.mpr (by simpa [hsetEq] using hi)
      simp [htrue, hi]
    · have hfalse : O which q = false := by
        cases hq : O which q with
        | false => rfl
        | true => exact (hi (by simpa [hsetEq] using hExactQ.mp hq)).elim
      simp [hfalse, hi]
  have hqReg : c₁.registers 6 = List.ofFn q := by
    simpa [q, finsetMembershipBits] using hregs6
  let targetControl : Fin 28 :=
    if (if which then M₂ else M₁).Indep (S : Set (Fin n))
    then ⟨11, by omega⟩ else ⟨10, by omega⟩
  have hprogram : exchangeCandidateQueryProgram which c₁.control =
      .query which ⟨6, by omega⟩ ⟨10, by omega⟩ ⟨11, by omega⟩ := by
    simp [exchangeCandidateQueryProgram, hcontrol]
  have hstep : machineStep (exchangeCandidateQueryProgram which) O (bits t) c₁ =
      { registers := c₁.registers
        control := targetControl
        output := c₁.output
        oracleCalls := c₁.oracleCalls + 1
        bitOperations := c₁.bitOperations + (2 * n + 1) } := by
    simp [machineStep, hprogram, hout, hqReg, hOracle, hlen, targetControl]
    omega
  have hrunQ : execution (exchangeCandidateQueryProgram which) O c bits (t + 1) =
      machineStep (exchangeCandidateQueryProgram which) O (bits t) c₁ := by
    simp [c₁, execution]
  dsimp only
  rw [hrunQ, hstep]
  refine ⟨?_, hregs6, hregs7, hregs8, hregs9, hout, ?_, ?_⟩
  · simp [targetControl, S] <;> split_ifs <;> rfl
  · rw [hcalls]
  · rw [hcost]


 theorem CountingMatroid.Bridge.exchangeCandidateQueryProgram_correct {n : ℕ}
    (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n)) (u v : Fin n)
    (which : Bool) (O : IndependenceOracle n)
    (hExact : ExactOracles M₁ M₂ O) (bits : ℕ → Bool)
    (c : MachineConfig 2 27)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = finsetMembershipBits I)
    (h7 : c.registers 7 = List.replicate u.val true)
    (h8 : c.registers 8 = []) (h9 : c.registers 9 = List.replicate v.val true) :
    let S := insert v (I.erase u)
    let t := 5 * u.val + 7 * v.val + 12
    let out := execution (exchangeCandidateQueryProgram which) O c bits (t + 1)
    out.control.val = (if (if which then M₂ else M₁).Indep (S : Set (Fin n)) then 11 else 10) ∧
      out.registers 6 = finsetMembershipBits S ∧ out.registers 7 = [] ∧
      out.registers 8 = [] ∧ out.registers 9 = [] ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls + 1 ∧
      out.bitOperations = c.bitOperations + t + (2 * n + 1) := by
  exact solution M₁ M₂ I u v which O hExact bits c hc ho h6 h7 h8 h9

