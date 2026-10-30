-- Prove2me | solution 1 for BitcoinHtlc.multisig_two
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T18:07:39.994692+00:00
-- url     : https://prove2.me/submissions/ecbe1414-ed3a-4dcc-90ba-58420f4f4bb1

import Definitions.Def_BitcoinHtlc
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinVerify_p2wsh_correct

open BitcoinHtlc
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

set_option linter.unusedSimpArgs false

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

private theorem serialize_length (n : Int) (k : Nat) (h : n.natAbs < 256 ^ k) :
    (BitcoinScript.serialize n).length ≤ k + 1 := by
  unfold serialize
  split
  · simp
  · have hm := natBytes_length k n.natAbs h
    dsimp only
    split
    · simp only [List.length_append, List.length_singleton]; omega
    · split
      · have : ∀ l : Bytes, (setTop l).length = l.length := by
          intro l; induction l with
          | nil => rfl
          | cons b r ih => cases r with
            | nil => rfl
            | cons c r' => simp only [setTop, List.length_cons] at ih ⊢; omega
        rw [this]; omega
      · omega

private theorem toNum_serialize5 (n : Int) (h : n.natAbs < 2 ^ 32) :
    toNum false 5 (serialize n) = some n := by
  unfold toNum
  have := serialize_length n 4 (by simpa using h)
  rw [if_neg (by omega)]
  simp [BitcoinScript.serialize_roundtrip]

private theorem serialize_two : serialize 2 = [2] := by decide +kernel

private theorem serialize_32 : serialize 32 = [0x20] := by decide +kernel

private theorem toNum_two : toNum false nDefaultMaxNumSize (serialize 2) = some 2 := by
  rw [serialize_two]; rfl

/-- The script number of a length equals `serialize 32` exactly for length 32. -/
private theorem serialize_length_eq_32 (n : Nat) : (serialize (n : Int) = serialize 32) ↔ n = 32 := by
  constructor
  · intro h
    have h' := congrArg setVch h
    rw [BitcoinScript.serialize_roundtrip, BitcoinScript.serialize_roundtrip] at h'
    omega
  · intro h; subst h; rfl

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

/-- `step` on a conditional opcode (`OP_IF`, `OP_NOTIF`, `OP_ELSE`, `OP_ENDIF`), executing or not. -/
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

private theorem execOp_notif_exec (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_NOTIF s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := rest, vfExec := (!castToBool top) :: s.vfExec } := by
  rfl

private theorem execOp_if_skip (f : Flags) (o : Oracle) (s : State) :
    execOp f o false OP_IF s = some { s with vfExec := false :: s.vfExec } := by
  rfl

private theorem execOp_notif_skip (f : Flags) (o : Oracle) (s : State) :
    execOp f o false OP_NOTIF s = some { s with vfExec := false :: s.vfExec } := by
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

private theorem execOp_dup (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_DUP s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := top :: top :: rest } := by
  rfl

private theorem execOp_swap (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_SWAP s = match s.stack with
      | a :: b :: rest => some { s with stack := b :: a :: rest }
      | _ => none := by
  rfl

private theorem execOp_size (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_SIZE s = match s.stack with
      | [] => none
      | top :: _ => some { s with stack := serialize (top.length : Int) :: s.stack } := by
  rfl

private theorem execOp_hash160 (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_HASH160 s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := o.hash160 top :: rest } := by
  rfl

private theorem execOp_equal (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_EQUAL s = match s.stack with
      | a :: b :: rest => some { s with stack := boolBytes (decide (b = a)) :: rest }
      | _ => none := by
  rfl

private theorem execOp_equalverify (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_EQUALVERIFY s = match s.stack with
      | a :: b :: rest => if decide (b = a) then some { s with stack := rest } else none
      | _ => none := by
  rfl

private theorem execOp_checksig (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_CHECKSIG s = match s.stack with
      | pubkey :: sig :: rest =>
        match o.checkSig sig pubkey with
        | none => none
        | some ok => some { s with stack := boolBytes ok :: rest }
      | _ => none := by
  rfl

private theorem execOp_cltv (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_CHECKLOCKTIMEVERIFY s =
      if !f.cltv then some s
      else match s.stack with
        | [] => none
        | top :: _ =>
          match toNum false 5 top with
          | none => none
          | some n => if n < 0 then none else if !o.checkLockTime n then none else some s := by
  rfl

/-- The 2-of-2 matching loop: both signatures must verify against their own key, the top signature
against the top key. -/
theorem solution (o : Oracle) (s1 s2 k1 k2 : Bytes) :
    BitcoinScript.multisigLoop o [s1, s2] [k1, k2] = some true ↔
      o.checkSig s1 k1 = some true ∧ o.checkSig s2 k2 = some true := by
  simp only [multisigLoop]
  cases o.checkSig s1 k1 with
  | none => simp
  | some ok1 =>
    cases ok1
    · simp
    · simp only [ite_true, List.length_cons, List.length_nil, Nat.lt_irrefl, ite_false]
      cases o.checkSig s2 k2 with
      | none => simp
      | some ok2 => cases ok2 <;> simp
