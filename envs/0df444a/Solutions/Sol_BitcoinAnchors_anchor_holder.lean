-- Prove2me | solution 1 for BitcoinAnchors.anchor_holder
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T20:24:54.717067+00:00
-- url     : https://prove2.me/submissions/044efbc1-87af-4714-9ddc-07ceea19950e

import Definitions.Def_BitcoinAnchors
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinVerify_p2wsh_correct
import Theorems.Thm_BitcoinToLocal_csv_step
import Theorems.Thm_BitcoinToLocal_csv_concrete
import Theorems.Thm_BitcoinToLocal_lightning_delay
import Theorems.Thm_BitcoinHtlc_cltv_step
import Theorems.Thm_BitcoinSig_checkSig_empty
import Theorems.Thm_BitcoinAnchors_anchor_eval

open BitcoinAnchors
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

private theorem execOp_cms (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_CHECKMULTISIG s =
      match s.stack with
      | [] => none
      | nk :: rest =>
        match toNum false nDefaultMaxNumSize nk with
        | none => none
        | some nKeys =>
          if nKeys < 0 || (MAX_PUBKEYS_PER_MULTISIG : Int) < nKeys then none
          else
            let opCount := s.opCount + nKeys.toNat
            if MAX_OPS_PER_SCRIPT < opCount then none
            else
              let keys := rest.take nKeys.toNat
              let rest := rest.drop nKeys.toNat
              if keys.length ≠ nKeys.toNat then none
              else match rest with
              | [] => none
              | ns :: rest =>
                match toNum false nDefaultMaxNumSize ns with
                | none => none
                | some nSigs =>
                  if nSigs < 0 || nKeys < nSigs then none
                  else
                    let sigs := rest.take nSigs.toNat
                    let rest := rest.drop nSigs.toNat
                    if sigs.length ≠ nSigs.toNat then none
                    else match multisigLoop o sigs keys with
                    | none => none
                    | some ok =>
                      match rest with
                      | [] => none
                      | dummy :: rest =>
                        if f.nulldummy && !dummy.isEmpty then none
                        else some { s with stack := boolBytes ok :: rest, opCount := opCount } := by
  rfl

/-- `OP_CHECKMULTISIG` on the stack `2 k1 k2 2 r` (top first): the two keys and then two signatures
and a dummy are consumed from `r`. -/
private theorem cms_two (f : Flags) (o : Oracle) (k1 k2 : Bytes) (r : List Bytes) (alt : List Bytes) (vf : List Bool)
    (k : Nat) (hop : k + 2 ≤ MAX_OPS_PER_SCRIPT) :
    execOp f o true OP_CHECKMULTISIG ⟨serialize 2 :: k1 :: k2 :: serialize 2 :: r, alt, vf, k⟩ =
      match r with
      | s1 :: s2 :: dummy :: rest =>
        match multisigLoop o [s1, s2] [k1, k2] with
        | none => none
        | some ok =>
          if f.nulldummy && !dummy.isEmpty then none
          else some ⟨boolBytes ok :: rest, alt, vf, k + 2⟩
      | _ => none := by
  rw [execOp_cms]
  dsimp only
  rw [toNum_two]
  dsimp only
  rw [if_neg (by decide)]
  simp only [Int.reduceToNat, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, not_true_eq_false, ite_false]
  rw [if_neg (by simp only [MAX_OPS_PER_SCRIPT] at hop ⊢; omega)]
  rw [toNum_two]
  dsimp only
  rw [if_neg (by decide)]
  simp only [Int.reduceToNat]
  match r with
  | [] => rfl
  | [s1] => rfl
  | [s1, s2] =>
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, Nat.reduceAdd, not_true_eq_false, ite_false]
    cases multisigLoop o [s1, s2] [k1, k2] <;> rfl
  | s1 :: s2 :: dummy :: rest =>
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, Nat.reduceAdd, not_true_eq_false, ite_false]

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

private theorem allTrue_nil : allTrue [] = true := rfl

private theorem allTrue_t : allTrue [true] = true := rfl

private theorem allTrue_f : allTrue [false] = false := rfl

private theorem allTrue_tt : allTrue [true, true] = true := rfl

private theorem allTrue_ft : allTrue [false, true] = false := rfl

private theorem allTrue_tf : allTrue [true, false] = false := rfl

private theorem allTrue_ff : allTrue [false, false] = false := rfl

private theorem run_op_skip (f : Flags) (o : Oracle) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (c : BitcoinScript.Byte) (rest : Script)
    (hc16 : OP_16 < c) (hcount : k + 1 ≤ MAX_OPS_PER_SCRIPT) (hdis : isDisabled c = false)
    (hexec : allTrue vf = false) (hcond : ¬ (OP_IF ≤ c ∧ c ≤ OP_ENDIF))
    (hstk : st.length + alt.length ≤ MAX_STACK_SIZE) :
    run f o ⟨st, alt, vf, k⟩ (.op c :: rest) = run f o ⟨st, alt, vf, k + 1⟩ rest := by
  rw [run, step_op_skip f o ⟨st, alt, vf, k⟩ c hc16 hcount hdis hexec hcond, if_neg (by simpa using hstk)]

private theorem run_push_skip (f : Flags) (o : Oracle) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (d : Bytes) (rest : Script)
    (hd : d.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hexec : allTrue vf = false)
    (hstk : st.length + alt.length ≤ MAX_STACK_SIZE) :
    run f o ⟨st, alt, vf, k⟩ (.push d :: rest) = run f o ⟨st, alt, vf, k⟩ rest := by
  rw [run, step_push_skip f o ⟨st, alt, vf, k⟩ d hd hexec, if_neg (by simpa using hstk)]

private theorem run_num_skip (f : Flags) (o : Oracle) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (n : Int) (rest : Script)
    (hn : (serialize n).length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hexec : allTrue vf = false)
    (hstk : st.length + alt.length ≤ MAX_STACK_SIZE) :
    run f o ⟨st, alt, vf, k⟩ (numInstr n :: rest) = run f o ⟨st, alt, vf, k⟩ rest := by
  rw [run, numInstr_skip f o ⟨st, alt, vf, k⟩ n hn hexec, if_neg (by simpa using hstk)]

private theorem run_nil (f : Flags) (o : Oracle) (s : State) :
    run f o s [] = if s.vfExec.isEmpty then some s else none := by
  rw [run]

private theorem ser2_len : (serialize 2).length ≤ MAX_SCRIPT_ELEMENT_SIZE := by
  rw [serialize_two]; decide

private theorem ser32_len : (serialize 32).length ≤ MAX_SCRIPT_ELEMENT_SIZE := by
  rw [serialize_32]; decide

/-- `OP_CHECKSIG` against `pk` on the stack below the key: the verdict above whatever lies below. -/
private def sigResult (o : Oracle) (pk : Bytes) : List Bytes → Option (List Bytes)
  | sig :: r => (o.checkSig sig pk).map (fun ok => boolBytes ok :: r)
  | [] => none

/-- `2 k1 k2 2 OP_CHECKMULTISIG` on the stack below the keys: two signatures and a dummy consumed. -/
private def msResult (f : Flags) (o : Oracle) (k1 k2 : Bytes) : List Bytes → Option (List Bytes)
  | s1 :: s2 :: dummy :: r =>
    match multisigLoop o [s1, s2] [k1, k2] with
    | none => none
    | some ok => if f.nulldummy && !dummy.isEmpty then none else some (boolBytes ok :: r)
  | _ => none

private theorem execOp_checksigverify (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_CHECKSIGVERIFY s = match s.stack with
      | pubkey :: sig :: rest =>
        match o.checkSig sig pubkey with
        | none => none
        | some ok => if ok then some { s with stack := rest } else none
      | _ => none := by
  rfl

private theorem execOp_ifdup (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_IFDUP s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := if castToBool top then top :: top :: rest else top :: rest } := by
  rfl

private theorem serialize_one : serialize 1 = [1] := by decide +kernel

private theorem serialize_16 : serialize 16 = [16] := by decide +kernel

private theorem ser1_len : (serialize 1).length ≤ MAX_SCRIPT_ELEMENT_SIZE := by
  rw [serialize_one]; decide

private theorem ser16_len : (serialize 16).length ≤ MAX_SCRIPT_ELEMENT_SIZE := by
  rw [serialize_16]; decide

private theorem toRemote_run (f : Flags) (o : Oracle) (remoteKey sig : Bytes) (rest : List Bytes)
    (hrem : remoteKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hn : rest.length + 2 ≤ MAX_STACK_SIZE) :
    evalScript f o (sig :: rest) (toRemoteScript remoteKey) =
      if o.checkSig sig remoteKey = some true then
        (if CsvPasses f o 1 then some (serialize 1 :: rest) else none)
      else none := by
  simp only [MAX_STACK_SIZE] at hn
  unfold evalScript toRemoteScript State.initial
  -- push remoteKey
  rw [run, step_push_exec f o _ remoteKey hrem allTrue_nil]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_CHECKSIGVERIFY
  rw [run, step_op_exec f o _ OP_CHECKSIGVERIFY (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
  rw [execOp_checksigverify]
  dsimp only
  cases hcs : o.checkSig sig remoteKey with
  | none => simp
  | some ok =>
    cases ok with
    | false => simp
    | true =>
      simp only [ite_true, Option.some.injEq]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- 1
      rw [run, numInstr_exec f o _ 1 ser1_len allTrue_nil]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- OP_CHECKSEQUENCEVERIFY
      rw [run, step_op_exec f o _ OP_CHECKSEQUENCEVERIFY (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
      rw [BitcoinToLocal.csv_step f o _ 1 rest rfl (by decide)]
      by_cases hc : CsvPasses f o 1
      · rw [if_pos hc, if_pos hc]
        dsimp only
        rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        dsimp only
        rw [run_nil]
        rfl
      · rw [if_neg hc, if_neg hc]
        rfl

private theorem toRemote_run_nil (f : Flags) (o : Oracle) (remoteKey : Bytes)
    (hrem : remoteKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) :
    evalScript f o [] (toRemoteScript remoteKey) = none := by
  unfold evalScript toRemoteScript State.initial
  rw [run, step_push_exec f o _ remoteKey hrem allTrue_nil]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  rw [run, step_op_exec f o _ OP_CHECKSIGVERIFY (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
  rw [execOp_checksigverify]
  rfl

private theorem toRemote_run_large (f : Flags) (o : Oracle) (remoteKey sig : Bytes) (rest : List Bytes)
    (hrem : remoteKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hn : MAX_STACK_SIZE < rest.length + 2) :
    evalScript f o (sig :: rest) (toRemoteScript remoteKey) = none := by
  simp only [MAX_STACK_SIZE] at hn
  unfold evalScript toRemoteScript State.initial
  rw [run, step_push_exec f o _ remoteKey hrem allTrue_nil]
  rw [if_pos (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rfl

set_option maxHeartbeats 1000000 in

private theorem anchor_run (f : Flags) (o : Oracle) (fundingKey sig : Bytes) (rest : List Bytes)
    (hfk : fundingKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hn : rest.length + 2 ≤ MAX_STACK_SIZE) :
    evalScript f o (sig :: rest) (anchorScript fundingKey) =
      match o.checkSig sig fundingKey with
      | none => none
      | some true => some (boolBytes true :: rest)
      | some false => if CsvPasses f o 16 then some (serialize 16 :: rest) else none := by
  simp only [MAX_STACK_SIZE] at hn
  unfold evalScript anchorScript State.initial
  -- push fundingKey
  rw [run, step_push_exec f o _ fundingKey hfk allTrue_nil]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_CHECKSIG
  rw [run, step_op_exec f o _ OP_CHECKSIG (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
  rw [execOp_checksig]
  dsimp only
  cases o.checkSig sig fundingKey with
  | none => rfl
  | some ok =>
    dsimp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_IFDUP
    rw [run, step_op_exec f o _ OP_IFDUP (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
    rw [execOp_ifdup]
    dsimp only
    rw [castToBool_boolBytes]
    cases ok with
    | true =>
      simp only [ite_true]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- OP_NOTIF (the signature verified: skip the delay)
      rw [run, step_op_cond f o _ OP_NOTIF (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
      rw [allTrue_nil, execOp_notif_exec]
      dsimp only
      rw [castToBool_boolBytes]
      simp only [Bool.not_true]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [run_num_skip f o _ _ _ _ 16 _ ser16_len allTrue_f (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_CHECKSEQUENCEVERIFY _ (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_f (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      -- OP_ENDIF
      rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
      rw [execOp_endif]
      dsimp only
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [run_nil]
      rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- OP_NOTIF (a clean false: run the delay branch)
      rw [run, step_op_cond f o _ OP_NOTIF (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
      rw [allTrue_nil, execOp_notif_exec]
      dsimp only
      rw [castToBool_boolBytes]
      simp only [Bool.not_false]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- 16
      rw [run, numInstr_exec f o _ 16 ser16_len allTrue_t]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- OP_CHECKSEQUENCEVERIFY
      rw [run, step_op_exec f o _ OP_CHECKSEQUENCEVERIFY (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_t]
      rw [BitcoinToLocal.csv_step f o _ 16 rest rfl (by decide)]
      by_cases hc : CsvPasses f o 16
      · rw [if_pos hc, if_pos hc]
        dsimp only
        rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        dsimp only
        -- OP_ENDIF
        rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
        rw [execOp_endif]
        dsimp only
        rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        dsimp only
        rw [run_nil]
        rfl
      · rw [if_neg hc, if_neg hc]
        rfl

private theorem anchor_run_nil (f : Flags) (o : Oracle) (fundingKey : Bytes)
    (hfk : fundingKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) :
    evalScript f o [] (anchorScript fundingKey) = none := by
  unfold evalScript anchorScript State.initial
  rw [run, step_push_exec f o _ fundingKey hfk allTrue_nil]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  rw [run, step_op_exec f o _ OP_CHECKSIG (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
  rw [execOp_checksig]
  rfl

private theorem anchor_run_large (f : Flags) (o : Oracle) (fundingKey sig : Bytes) (rest : List Bytes)
    (hfk : fundingKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hn : MAX_STACK_SIZE < rest.length + 2) :
    evalScript f o (sig :: rest) (anchorScript fundingKey) = none := by
  simp only [MAX_STACK_SIZE] at hn
  unfold evalScript anchorScript State.initial
  rw [run, step_push_exec f o _ fundingKey hfk allTrue_nil]
  rw [if_pos (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rfl

/-- The key holder's witness `<sig>`: a valid signature spends the anchor at once (no delay check). -/
theorem solution (f : Flags) (o : Oracle) (fundingKey sig : Bytes)
    (hfk : fundingKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hcs : o.checkSig sig fundingKey = some true) :
    BitcoinScript.evalScript f o [sig] (BitcoinAnchors.anchorScript fundingKey) = some [[1]] := by
  rw [BitcoinAnchors.anchor_eval f o fundingKey sig hfk, hcs]
