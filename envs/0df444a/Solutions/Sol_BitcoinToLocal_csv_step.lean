-- Prove2me | solution 1 for BitcoinToLocal.csv_step
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:19:18.602335+00:00
-- url     : https://prove2.me/submissions/f6d1e0bf-a669-4fd2-b0a3-8caedd867b0f

import Definitions.Def_BitcoinToLocal
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinVerify_p2wsh_correct
import Theorems.Thm_BitcoinToLocal_serialize_length

open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

private theorem natBytes_length : ∀ (k n : Nat), n < 256 ^ k → (natBytes n).length ≤ k
  | 0, n, h => by
    have : n = 0 := by simp at h; omega
    subst this; rw [natBytes]; simp
  | k + 1, n, h => by
    rw [natBytes]
    split
    · simp
    · simp only [List.length_cons]
      have := natBytes_length k (n / 256) (by rw [Nat.pow_succ] at h; omega)
      omega

private theorem toNum_serialize5 (n : Int) (h : n.natAbs < 2 ^ 32) :
    toNum false 5 (serialize n) = some n := by
  unfold toNum
  have := BitcoinToLocal.serialize_length n 4 (by simpa using h)
  rw [if_neg (by omega)]
  simp [BitcoinScript.serialize_roundtrip]

private theorem castToBool_boolBytes (b : Bool) : castToBool (boolBytes b) = b := by
  cases b <;> rfl

/-- `step` on an executing state for an opcode above `OP_16`. -/
private theorem step_op_exec (f : Flags) (o : Oracle) (s : State) (c : BitcoinScript.Byte)
    (hc16 : OP_16 < c) (hcount : s.opCount + 1 ≤ MAX_OPS_PER_SCRIPT) (hdis : isDisabled c = false)
    (hexec : allTrue s.vfExec = true) :
    step f o s (.op c) =
      match execOp f o true c { s with opCount := s.opCount + 1 } with
      | none => none
      | some s' => if MAX_STACK_SIZE < s'.stack.length + s'.altstack.length then none else some s' := by
  unfold step
  simp only [hexec, hdis, hc16, decide_true, Bool.true_and, decide_eq_true_eq, Bool.true_or,
    ite_true, Bool.false_eq_true, ite_false]
  rw [if_neg (by omega)]
  rfl

/-- `step` on a non-executing state for an opcode above `OP_16` outside `OP_IF … OP_ENDIF`. -/
private theorem step_op_skip (f : Flags) (o : Oracle) (s : State) (c : BitcoinScript.Byte)
    (hc16 : OP_16 < c) (hcount : s.opCount + 1 ≤ MAX_OPS_PER_SCRIPT) (hdis : isDisabled c = false)
    (hexec : allTrue s.vfExec = false) (hcond : ¬ (OP_IF ≤ c ∧ c ≤ OP_ENDIF)) :
    step f o s (.op c) =
      if MAX_STACK_SIZE < s.stack.length + s.altstack.length then none
      else some { s with opCount := s.opCount + 1 } := by
  unfold step
  simp only [hexec, hdis, hc16, decide_true, Bool.true_and, decide_eq_true_eq, Bool.false_or,
    ite_true, Bool.false_eq_true, ite_false]
  rw [if_neg (show ¬ MAX_OPS_PER_SCRIPT < s.opCount + 1 by simp only [MAX_OPS_PER_SCRIPT] at hcount ⊢; omega)]
  have : (decide (OP_IF ≤ c) && decide (c ≤ OP_ENDIF)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases hA : OP_IF ≤ c
    · exact Or.inr (fun hB => hcond ⟨hA, hB⟩)
    · exact Or.inl hA
  rw [this]
  simp

/-- `step` on a conditional opcode (`OP_IF`, `OP_ELSE`, `OP_ENDIF`), executing or not. -/
private theorem step_op_cond (f : Flags) (o : Oracle) (s : State) (c : BitcoinScript.Byte)
    (hc16 : OP_16 < c) (hcount : s.opCount + 1 ≤ MAX_OPS_PER_SCRIPT) (hdis : isDisabled c = false)
    (hcond : OP_IF ≤ c ∧ c ≤ OP_ENDIF) :
    step f o s (.op c) =
      match execOp f o (allTrue s.vfExec) c { s with opCount := s.opCount + 1 } with
      | none => none
      | some s' => if MAX_STACK_SIZE < s'.stack.length + s'.altstack.length then none else some s' := by
  unfold step
  have : (OP_IF ≤ c && c ≤ OP_ENDIF) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hcond
  simp only [hdis, hc16, this, decide_true, Bool.true_and, decide_eq_true_eq, Bool.or_true,
    ite_true, Bool.false_eq_true, ite_false]
  rw [if_neg (by omega)]
  rfl

private theorem step_push_exec (f : Flags) (o : Oracle) (s : State) (d : Bytes)
    (hd : d.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hexec : allTrue s.vfExec = true) :
    step f o s (.push d) =
      if MAX_STACK_SIZE < s.stack.length + 1 + s.altstack.length then none
      else some { s with stack := d :: s.stack } := by
  dsimp only [step]
  rw [if_neg (show ¬ MAX_SCRIPT_ELEMENT_SIZE < d.length by omega)]
  simp [hexec]

private theorem step_push_skip (f : Flags) (o : Oracle) (s : State) (d : Bytes)
    (hd : d.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hexec : allTrue s.vfExec = false) :
    step f o s (.push d) =
      if MAX_STACK_SIZE < s.stack.length + s.altstack.length then none else some s := by
  dsimp only [step]
  rw [if_neg (show ¬ MAX_SCRIPT_ELEMENT_SIZE < d.length by omega)]
  simp [hexec]

private theorem execOp_if_exec (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_IF s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := rest, vfExec := castToBool top :: s.vfExec } := by
  rfl

private theorem execOp_else (f : Flags) (o : Oracle) (e : Bool) (s : State) :
    execOp f o e OP_ELSE s = match s.vfExec with
      | [] => none
      | b :: rest => some { s with vfExec := (!b) :: rest } := by
  cases e <;> rfl

private theorem execOp_endif (f : Flags) (o : Oracle) (e : Bool) (s : State) :
    execOp f o e OP_ENDIF s = match s.vfExec with
      | [] => none
      | _ :: rest => some { s with vfExec := rest } := by
  cases e <;> rfl

private theorem execOp_drop (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_DROP s = match s.stack with
      | [] => none
      | _ :: rest => some { s with stack := rest } := by
  rfl

private theorem execOp_checksig (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_CHECKSIG s = match s.stack with
      | pubkey :: sig :: rest =>
        match o.checkSig sig pubkey with
        | none => none
        | some ok => some { s with stack := boolBytes ok :: rest }
      | _ => none := by
  rfl

private theorem execOp_csv (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_CHECKSEQUENCEVERIFY s =
      if !f.csv then some s
      else match s.stack with
        | [] => none
        | top :: _ =>
          match toNum false 5 top with
          | none => none
          | some n =>
            if n < 0 then none
            else if (n.toNat &&& BitcoinScript.SEQUENCE_LOCKTIME_DISABLE_FLAG) != 0 then some s
            else if !o.checkSequence n then none else some s := by
  rfl

/-- `OP_CHECKSEQUENCEVERIFY` on a stack whose top is the serialization of a 5-byte number. -/
theorem solution (f : Flags) (o : Oracle) (s : State) (delay : Int) (rest : List Bytes)
    (hs : s.stack = BitcoinScript.serialize delay :: rest) (hd : delay.natAbs < 2 ^ 32) :
    BitcoinScript.execOp f o true BitcoinScript.OP_CHECKSEQUENCEVERIFY s =
      if BitcoinToLocal.CsvPasses f o delay then some s else none := by
  rw [execOp_csv, hs]
  dsimp only
  rw [toNum_serialize5 delay hd]
  dsimp only
  by_cases hc : f.csv = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases h0 : delay < 0
    · rw [if_pos h0, if_neg]
      unfold CsvPasses; simp only [hc, Bool.true_eq_false, false_or, not_and]; intro; omega
    · rw [if_neg h0]
      by_cases hdis : (delay.toNat &&& BitcoinScript.SEQUENCE_LOCKTIME_DISABLE_FLAG) ≠ 0
      · have h' : (delay.toNat &&& BitcoinScript.SEQUENCE_LOCKTIME_DISABLE_FLAG != 0) = true := by simpa using hdis
        rw [if_pos h', if_pos]
        unfold CsvPasses; exact Or.inr ⟨by omega, Or.inl hdis⟩
      · have h' : (delay.toNat &&& BitcoinScript.SEQUENCE_LOCKTIME_DISABLE_FLAG != 0) = false := by simpa using hdis
        rw [if_neg (by simp [h'])]
        by_cases hcs : o.checkSequence delay = true
        · simp only [hcs, Bool.not_true, Bool.false_eq_true, ite_false]
          rw [if_pos]
          unfold CsvPasses; exact Or.inr ⟨by omega, Or.inr hcs⟩
        · simp only [Bool.not_eq_true] at hcs
          simp only [hcs, Bool.not_false, ite_true]
          rw [if_neg]
          unfold CsvPasses
          simp only [hc, Bool.true_eq_false, false_or, hcs, Bool.false_eq_true, or_false, not_and]
          intro; exact hdis
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.not_false, ite_true]
    rw [if_pos]
    unfold CsvPasses; exact Or.inl hc
