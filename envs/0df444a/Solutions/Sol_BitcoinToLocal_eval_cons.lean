-- Prove2me | solution 1 for BitcoinToLocal.eval_cons
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:19:38.56469+00:00
-- url     : https://prove2.me/submissions/d32dee35-51d9-45f5-bede-5ef361c9b0d6

import Definitions.Def_BitcoinToLocal
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinVerify_p2wsh_correct
import Theorems.Thm_BitcoinToLocal_csv_step
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

private theorem step_op_n (f : Flags) (o : Oracle) (s : State) (c : BitcoinScript.Byte)
    (hc16 : c ≤ OP_16) (hdis : isDisabled c = false) (hcond : ¬ OP_IF ≤ c) :
    step f o s (.op c) =
      if allTrue s.vfExec then
        match execOp f o true c s with
        | none => none
        | some s' => if MAX_STACK_SIZE < s'.stack.length + s'.altstack.length then none else some s'
      else if MAX_STACK_SIZE < s.stack.length + s.altstack.length then none else some s := by
  unfold step
  have h1 : decide (OP_16 < c) = false := by simp only [decide_eq_false_iff_not]; exact fun h => absurd hc16 (BitVec.not_le.mpr h)
  have h2 : decide (OP_IF ≤ c) = false := by simp only [decide_eq_false_iff_not]; exact hcond
  simp only [h1, h2, hdis, Bool.false_and, Bool.false_eq_true, ite_false, Bool.or_false]
  cases allTrue s.vfExec
  · simp
  · simp only [ite_true]
    rfl

private def opByte (n : Int) : BitcoinScript.Byte := BitVec.ofNat 8 (n + (OP_1.toNat - 1)).toNat

private theorem opn_facts (n : Int) (hn : n = -1 ∨ (1 ≤ n ∧ n ≤ 16)) :
    opByte n ≤ OP_16 ∧ isDisabled (opByte n) = false ∧ ¬ OP_IF ≤ opByte n ∧
      (opByte n == OP_1NEGATE || (OP_1 ≤ opByte n && opByte n ≤ OP_16)) = true ∧
      ((opByte n).toNat : Int) - ((OP_1.toNat : Int) - 1) = n := by
  have h : n = -1 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem numInstr_exec (f : Flags) (o : Oracle) (s : State) (n : Int)
    (hn : (serialize n).length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hexec : allTrue s.vfExec = true) :
    step f o s (numInstr n) =
      if MAX_STACK_SIZE < s.stack.length + 1 + s.altstack.length then none
      else some { s with stack := serialize n :: s.stack } := by
  unfold numInstr
  split
  · rename_i h
    obtain ⟨h1, h2, h3, h4, h5⟩ := opn_facts n h
    rw [show (BitVec.ofNat 8 (n + (OP_1.toNat - 1)).toNat) = opByte n from rfl]
    rw [step_op_n f o s _ h1 h2 h3, if_pos hexec]
    unfold execOp
    rw [if_pos h4]
    simp only [pushNum, h5, List.length_cons]
  · exact step_push_exec f o s _ hn hexec

private theorem numInstr_skip (f : Flags) (o : Oracle) (s : State) (n : Int)
    (hn : (serialize n).length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hexec : allTrue s.vfExec = false) :
    step f o s (numInstr n) =
      if MAX_STACK_SIZE < s.stack.length + s.altstack.length then none else some s := by
  unfold numInstr
  split
  · rename_i h
    obtain ⟨h1, h2, h3, -, -⟩ := opn_facts n h
    rw [show (BitVec.ofNat 8 (n + (OP_1.toNat - 1)).toNat) = opByte n from rfl]
    rw [step_op_n f o s _ h1 h2 h3, if_neg (by simp [hexec])]
  · exact step_push_skip f o s _ hn hexec

private theorem and_two_pow_eq_zero (n k : Nat) (h : n < 2 ^ k) : n &&& 2 ^ k = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hi : k = i
  · subst hi; rw [Nat.testBit_lt_two_pow h]; rfl
  · simp [hi]

example (n : Nat) (h : n < 2 ^ 16) : n &&& (2 ^ 22 ||| 0xffff) = n := by
  rw [Nat.and_or_distrib_left, and_two_pow_eq_zero n 22 (by omega), Nat.zero_or]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 16) h

private theorem allTrue_nil : allTrue [] = true := rfl

private theorem allTrue_true : allTrue [true] = true := rfl

private theorem allTrue_false : allTrue [false] = false := rfl

set_option maxHeartbeats 1000000 in

private theorem run_cons (f : Flags) (o : Oracle) (rev dpk b : Bytes) (delay : Int) (tl : List Bytes)
    (hrev : rev.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) (htl : tl.length + 1 ≤ MAX_STACK_SIZE) :
    evalScript f o (b :: tl) (toLocalScript rev delay dpk) =
      match tl with
      | [] => none
      | sig :: rest =>
        if castToBool b then (o.checkSig sig rev).map (fun ok => boolBytes ok :: rest)
        else if CsvPasses f o delay then (o.checkSig sig dpk).map (fun ok => boolBytes ok :: rest) else none := by
  have hser : (serialize delay).length ≤ MAX_SCRIPT_ELEMENT_SIZE :=
    Nat.le_trans (BitcoinToLocal.serialize_length delay 4 (by simpa using hd)) (by decide)
  simp only [MAX_STACK_SIZE] at htl
  unfold evalScript toLocalScript State.initial
  -- OP_IF
  rw [run, step_op_cond f o _ OP_IF (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
  rw [allTrue_nil, execOp_if_exec]
  dsimp only
  rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  by_cases hb : castToBool b = true
  · rw [hb]
    -- push rev (executing)
    rw [run, step_push_exec f o _ rev hrev allTrue_true]
    rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_ELSE
    rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
    rw [execOp_else]
    dsimp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- the number (skipped)
    rw [run, numInstr_skip f o _ delay hser allTrue_false]
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_CHECKSEQUENCEVERIFY (skipped)
    rw [run, step_op_skip f o _ OP_CHECKSEQUENCEVERIFY (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_false (by decide)]
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_DROP (skipped)
    rw [run, step_op_skip f o _ OP_DROP (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_false (by decide)]
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- push dpk (skipped)
    rw [run, step_push_skip f o _ dpk hdpk allTrue_false]
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_ENDIF
    rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
    rw [execOp_endif]
    dsimp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_CHECKSIG
    rw [run, step_op_exec f o _ OP_CHECKSIG (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
    rw [execOp_checksig]
    cases tl with
    | nil => rfl
    | cons sig rest =>
      dsimp only
      cases o.checkSig sig rev with
      | none => rfl
      | some ok =>
        dsimp only
        simp only [List.length_cons, List.length_nil] at htl ⊢
        rw [if_neg (by simp only [MAX_STACK_SIZE]; omega)]
        dsimp only
        simp [run]
  · simp only [Bool.not_eq_true] at hb
    rw [hb]
    -- push rev (skipped)
    rw [run, step_push_skip f o _ rev hrev allTrue_false]
    rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_ELSE
    rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
    rw [execOp_else]
    dsimp only
    rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- the number (executing)
    rw [run, numInstr_exec f o _ delay hser allTrue_true]
    rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_CHECKSEQUENCEVERIFY
    rw [run, step_op_exec f o _ OP_CHECKSEQUENCEVERIFY (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_true]
    rw [BitcoinToLocal.csv_step f o _ delay tl rfl hd]
    by_cases hcsv : CsvPasses f o delay
    · rw [if_pos hcsv]
      dsimp only
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- OP_DROP
      rw [run, step_op_exec f o _ OP_DROP (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_true]
      rw [execOp_drop]
      dsimp only
      rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- push dpk
      rw [run, step_push_exec f o _ dpk hdpk allTrue_true]
      rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- OP_ENDIF
      rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
      rw [execOp_endif]
      dsimp only
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- OP_CHECKSIG
      rw [run, step_op_exec f o _ OP_CHECKSIG (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
      rw [execOp_checksig]
      cases tl with
      | nil => rfl
      | cons sig rest =>
        dsimp only
        cases o.checkSig sig dpk with
        | none => simp [hcsv]
        | some ok =>
          dsimp only
          simp only [List.length_cons, List.length_nil] at htl ⊢
          rw [if_neg (by simp only [MAX_STACK_SIZE]; omega)]
          dsimp only
          simp [run, hcsv]
    · rw [if_neg hcsv]
      cases tl with
      | nil => rfl
      | cons sig rest => simp [hcsv]

/-- The script on a stack `b :: tl` (top first) of admissible size: it fails unless `tl` is a single
signature, otherwise it leaves the result of the chosen signature check above whatever lies below. -/
theorem solution (f : Flags) (o : Oracle) (rev dpk b : Bytes) (delay : Int) (tl : List Bytes)
    (hrev : rev.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) (htl : tl.length + 1 ≤ BitcoinScript.MAX_STACK_SIZE) :
    BitcoinScript.evalScript f o (b :: tl) (BitcoinToLocal.toLocalScript rev delay dpk) =
      match tl with
      | [] => none
      | sig :: rest =>
        if BitcoinScript.castToBool b then (o.checkSig sig rev).map (fun ok => BitcoinScript.boolBytes ok :: rest)
        else if BitcoinToLocal.CsvPasses f o delay then (o.checkSig sig dpk).map (fun ok => BitcoinScript.boolBytes ok :: rest)
        else none :=
  run_cons f o rev dpk b delay tl hrev hdpk hd htl
