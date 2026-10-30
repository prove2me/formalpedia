-- Prove2me | solution 1 for BitcoinAnchors.anchor_anyone_concrete
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T20:26:26.758996+00:00
-- url     : https://prove2.me/submissions/f4ee4d52-51d9-4d37-937c-011eca5bd2d6

import Definitions.Def_BitcoinAnchors
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinVerify_p2wsh_correct
import Theorems.Thm_BitcoinToLocal_csv_step
import Theorems.Thm_BitcoinToLocal_csv_concrete
import Theorems.Thm_BitcoinToLocal_lightning_delay
import Theorems.Thm_BitcoinHtlc_cltv_step
import Theorems.Thm_BitcoinSig_checkSig_empty
import Theorems.Thm_BitcoinAnchors_anchor_p2wsh_spend

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

set_option maxHeartbeats 1000000 in

private theorem offered_tailA (f : Flags) (o : Oracle) (remoteKey localKey payHash x : Bytes) (rest : List Bytes) (k : Nat)
    (hrem : remoteKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hloc : localKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hpay : payHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hk : k + 25 ≤ MAX_OPS_PER_SCRIPT)
    (hn : rest.length + 1 ≤ MAX_STACK_SIZE) :
    (run f o ⟨x :: rest, [], [true], k⟩
      [.op OP_CHECKSIG,
       .op OP_ELSE, .push remoteKey, .op OP_SWAP, .op OP_SIZE, numInstr 32, .op OP_EQUAL,
       .op OP_NOTIF, .op OP_DROP, numInstr 2, .op OP_SWAP, .push localKey, numInstr 2, .op OP_CHECKMULTISIG,
       .op OP_ELSE, .op OP_HASH160, .push payHash, .op OP_EQUALVERIFY, .op OP_CHECKSIG,
       .op OP_ENDIF,
       numInstr 1, .op OP_CHECKSEQUENCEVERIFY, .op OP_DROP,
       .op OP_ENDIF]).map State.stack = sigResult o x rest := by
  simp only [MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT] at hn hk
  -- OP_CHECKSIG
  rw [run, step_op_exec f o _ OP_CHECKSIG (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
  rw [execOp_checksig]
  cases rest with
  | nil => rfl
  | cons sig r =>
    dsimp only [sigResult]
    cases o.checkSig sig x with
    | none => rfl
    | some ok =>
      dsimp only
      simp only [List.length_cons] at hn
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- OP_ELSE
      rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
      rw [execOp_else]
      dsimp only
      simp only [Bool.not_true]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [run_push_skip f o _ _ _ _ remoteKey _ hrem allTrue_f (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_SWAP _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_f (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_SIZE _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_f (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_num_skip f o _ _ _ _ 32 _ ser32_len allTrue_f (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_EQUAL _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_f (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      -- OP_NOTIF (not executing)
      rw [run, step_op_cond f o _ OP_NOTIF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
      rw [allTrue_f, execOp_notif_skip]
      dsimp only
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [run_op_skip f o _ _ _ _ OP_DROP _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ff (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_num_skip f o _ _ _ _ 2 _ ser2_len allTrue_ff (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_SWAP _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ff (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_push_skip f o _ _ _ _ localKey _ hloc allTrue_ff (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_num_skip f o _ _ _ _ 2 _ ser2_len allTrue_ff (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_CHECKMULTISIG _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ff (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      -- OP_ELSE (inner)
      rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
      rw [execOp_else]
      dsimp only
      simp only [Bool.not_false]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [run_op_skip f o _ _ _ _ OP_HASH160 _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tf (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_push_skip f o _ _ _ _ payHash _ hpay allTrue_tf (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_EQUALVERIFY _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tf (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_CHECKSIG _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tf (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      -- OP_ENDIF, OP_ENDIF
      rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
      rw [execOp_endif]
      dsimp only
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- 1 OP_CHECKSEQUENCEVERIFY OP_DROP (skipped)
      rw [run_num_skip f o _ _ _ _ 1 _ ser1_len allTrue_f (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_CHECKSEQUENCEVERIFY _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_f (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_DROP _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_f (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
      rw [execOp_endif]
      dsimp only
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [run_nil]
      rfl

-- Branch B1 (timeout, 2-of-2) of the offered script, from `OP_DROP` on.

set_option maxHeartbeats 1000000 in

private theorem offered_tailB1 (f : Flags) (o : Oracle) (remoteKey localKey payHash x : Bytes) (rest : List Bytes) (k : Nat)
    (hloc : localKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hk : k + 25 ≤ MAX_OPS_PER_SCRIPT) (hn : rest.length + 4 ≤ MAX_STACK_SIZE) :
    (run f o ⟨x :: remoteKey :: rest, [], [true, true], k⟩
      [.op OP_DROP, numInstr 2, .op OP_SWAP, .push localKey, numInstr 2, .op OP_CHECKMULTISIG,
       .op OP_ELSE, .op OP_HASH160, .push payHash, .op OP_EQUALVERIFY, .op OP_CHECKSIG,
       .op OP_ENDIF,
       numInstr 1, .op OP_CHECKSEQUENCEVERIFY, .op OP_DROP,
       .op OP_ENDIF]).map State.stack =
      if CsvPasses f o 1 then msResult f o localKey remoteKey rest else none := by
  simp only [MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT] at hn hk
  -- OP_DROP
  rw [run, step_op_exec f o _ OP_DROP (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tt]
  rw [execOp_drop]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- 2
  rw [run, numInstr_exec f o _ 2 ser2_len allTrue_tt]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_SWAP
  rw [run, step_op_exec f o _ OP_SWAP (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tt]
  rw [execOp_swap]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- push localKey
  rw [run, step_push_exec f o _ localKey hloc allTrue_tt]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- 2
  rw [run, numInstr_exec f o _ 2 ser2_len allTrue_tt]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_CHECKMULTISIG
  rw [run, step_op_exec f o _ OP_CHECKMULTISIG (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tt]
  dsimp only
  rw [cms_two f o localKey remoteKey rest [] [true, true] _ (by simp only [MAX_OPS_PER_SCRIPT]; omega)]
  match rest with
  | [] => simp only [msResult, ite_self]; rfl
  | [s1] => simp only [msResult, ite_self]; rfl
  | [s1, s2] => simp only [msResult, ite_self]; rfl
  | s1 :: s2 :: dummy :: r =>
    dsimp only [msResult]
    simp only [List.length_cons] at hn
    cases multisigLoop o [s1, s2] [localKey, remoteKey] with
    | none => rw [ite_self]; rfl
    | some ok =>
      dsimp only
      by_cases hd : (f.nulldummy && !dummy.isEmpty) = true
      · rw [if_pos hd, if_pos hd, ite_self]; rfl
      · rw [if_neg hd, if_neg hd]
        dsimp only
        rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        dsimp only
        -- OP_ELSE
        rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
        rw [execOp_else]
        dsimp only
        simp only [Bool.not_true]
        rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        dsimp only
        rw [run_op_skip f o _ _ _ _ OP_HASH160 _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ft (by decide)
          (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        rw [run_push_skip f o _ _ _ _ payHash _ hpay allTrue_ft (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        rw [run_op_skip f o _ _ _ _ OP_EQUALVERIFY _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ft (by decide)
          (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        rw [run_op_skip f o _ _ _ _ OP_CHECKSIG _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ft (by decide)
          (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        -- inner OP_ENDIF
        rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
        rw [execOp_endif]
        dsimp only
        rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        dsimp only
        -- 1 OP_CHECKSEQUENCEVERIFY OP_DROP
        rw [run, numInstr_exec f o _ 1 ser1_len allTrue_t]
        rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        dsimp only
        rw [run, step_op_exec f o _ OP_CHECKSEQUENCEVERIFY (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
        rw [BitcoinToLocal.csv_step f o _ 1 _ rfl (by decide)]
        by_cases hc1 : CsvPasses f o 1
        · rw [if_pos hc1, if_pos hc1]
          dsimp only
          rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          dsimp only
          rw [run, step_op_exec f o _ OP_DROP (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
          rw [execOp_drop]
          dsimp only
          rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          dsimp only
          -- outer OP_ENDIF
          rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
          rw [execOp_endif]
          dsimp only
          rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          dsimp only
          rw [run_nil]
          rfl
        · rw [if_neg hc1, if_neg hc1]
          rfl

-- Branch B2 (preimage) of the offered script, from `OP_DROP` on.

set_option maxHeartbeats 1000000 in

private theorem offered_tailB2 (f : Flags) (o : Oracle) (remoteKey localKey payHash x : Bytes) (rest : List Bytes) (k : Nat)
    (hloc : localKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hk : k + 25 ≤ MAX_OPS_PER_SCRIPT) (hn : rest.length + 3 ≤ MAX_STACK_SIZE) :
    (run f o ⟨x :: remoteKey :: rest, [], [false, true], k⟩
      [.op OP_DROP, numInstr 2, .op OP_SWAP, .push localKey, numInstr 2, .op OP_CHECKMULTISIG,
       .op OP_ELSE, .op OP_HASH160, .push payHash, .op OP_EQUALVERIFY, .op OP_CHECKSIG,
       .op OP_ENDIF,
       numInstr 1, .op OP_CHECKSEQUENCEVERIFY, .op OP_DROP,
       .op OP_ENDIF]).map State.stack =
      if o.hash160 x = payHash then (if CsvPasses f o 1 then sigResult o remoteKey rest else none) else none := by
  simp only [MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT] at hn hk
  rw [run_op_skip f o _ _ _ _ OP_DROP _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ft (by decide)
    (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rw [run_num_skip f o _ _ _ _ 2 _ ser2_len allTrue_ft (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rw [run_op_skip f o _ _ _ _ OP_SWAP _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ft (by decide)
    (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rw [run_push_skip f o _ _ _ _ localKey _ hloc allTrue_ft (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rw [run_num_skip f o _ _ _ _ 2 _ ser2_len allTrue_ft (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rw [run_op_skip f o _ _ _ _ OP_CHECKMULTISIG _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ft (by decide)
    (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  -- OP_ELSE
  rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
  rw [execOp_else]
  dsimp only
  simp only [Bool.not_false]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_HASH160
  rw [run, step_op_exec f o _ OP_HASH160 (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tt]
  rw [execOp_hash160]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- push payHash
  rw [run, step_push_exec f o _ payHash hpay allTrue_tt]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_EQUALVERIFY
  rw [run, step_op_exec f o _ OP_EQUALVERIFY (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tt]
  rw [execOp_equalverify]
  dsimp only
  by_cases hp : o.hash160 x = payHash
  · rw [if_pos (decide_eq_true hp), if_pos hp]
    dsimp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_CHECKSIG
    rw [run, step_op_exec f o _ OP_CHECKSIG (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tt]
    rw [execOp_checksig]
    cases rest with
    | nil => rw [show sigResult o remoteKey [] = none from rfl, ite_self]; rfl
    | cons sig r =>
      dsimp only [sigResult]
      cases o.checkSig sig remoteKey with
      | none => rw [show Option.map (fun ok => boolBytes ok :: r) (none : Option Bool) = none from rfl, ite_self]; rfl
      | some ok =>
        dsimp only
        simp only [List.length_cons] at hn
        rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        dsimp only
        -- inner OP_ENDIF
        rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
        rw [execOp_endif]
        dsimp only
        rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        dsimp only
        -- 1 OP_CHECKSEQUENCEVERIFY OP_DROP
        rw [run, numInstr_exec f o _ 1 ser1_len allTrue_t]
        rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        dsimp only
        rw [run, step_op_exec f o _ OP_CHECKSEQUENCEVERIFY (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
        rw [BitcoinToLocal.csv_step f o _ 1 _ rfl (by decide)]
        by_cases hc1 : CsvPasses f o 1
        · rw [if_pos hc1, if_pos hc1]
          dsimp only
          rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          dsimp only
          rw [run, step_op_exec f o _ OP_DROP (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
          rw [execOp_drop]
          dsimp only
          rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          dsimp only
          -- outer OP_ENDIF
          rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
          rw [execOp_endif]
          dsimp only
          rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          dsimp only
          rw [run_nil]
          rfl
        · rw [if_neg hc1, if_neg hc1]
          rfl
  · rw [if_neg (by rw [decide_eq_false hp]; decide), if_neg hp]
    rfl

-- Branch B (not the revocation key) of the offered script, from the (skipped) `OP_CHECKSIG` on.

set_option maxHeartbeats 1000000 in

private theorem offered_tailB (f : Flags) (o : Oracle) (remoteKey localKey payHash x : Bytes) (rest : List Bytes) (k : Nat)
    (hrem : remoteKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hloc : localKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hpay : payHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hk : k + 35 ≤ MAX_OPS_PER_SCRIPT)
    (hn : rest.length + 3 ≤ MAX_STACK_SIZE) :
    (run f o ⟨x :: rest, [], [false], k⟩
      [.op OP_CHECKSIG,
       .op OP_ELSE, .push remoteKey, .op OP_SWAP, .op OP_SIZE, numInstr 32, .op OP_EQUAL,
       .op OP_NOTIF, .op OP_DROP, numInstr 2, .op OP_SWAP, .push localKey, numInstr 2, .op OP_CHECKMULTISIG,
       .op OP_ELSE, .op OP_HASH160, .push payHash, .op OP_EQUALVERIFY, .op OP_CHECKSIG,
       .op OP_ENDIF,
       numInstr 1, .op OP_CHECKSEQUENCEVERIFY, .op OP_DROP,
       .op OP_ENDIF]).map State.stack =
      if MAX_STACK_SIZE < rest.length + 4 then none
      else if x.length = 32 then
        (if o.hash160 x = payHash then (if CsvPasses f o 1 then sigResult o remoteKey rest else none) else none)
      else (if CsvPasses f o 1 then msResult f o localKey remoteKey rest else none) := by
  simp only [MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT] at hn hk
  rw [run_op_skip f o _ _ _ _ OP_CHECKSIG _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_f (by decide)
    (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  -- OP_ELSE
  rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
  rw [execOp_else]
  dsimp only
  simp only [Bool.not_false]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- push remoteKey
  rw [run, step_push_exec f o _ remoteKey hrem allTrue_t]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_SWAP
  rw [run, step_op_exec f o _ OP_SWAP (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
  rw [execOp_swap]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_SIZE
  rw [run, step_op_exec f o _ OP_SIZE (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
  rw [execOp_size]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- 32
  rw [run, numInstr_exec f o _ 32 ser32_len allTrue_t]
  by_cases hg : MAX_STACK_SIZE < rest.length + 4
  · rw [if_pos (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE] at hg ⊢; omega), if_pos hg]
    rfl
  · rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE] at hg ⊢; omega), if_neg hg]
    dsimp only
    simp only [MAX_STACK_SIZE] at hg
    -- OP_EQUAL
    rw [run, step_op_exec f o _ OP_EQUAL (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
    rw [execOp_equal]
    dsimp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_NOTIF
    rw [run, step_op_cond f o _ OP_NOTIF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
    rw [allTrue_t, execOp_notif_exec]
    dsimp only
    by_cases h32 : x.length = 32
    · rw [decide_eq_true ((serialize_length_eq_32 _).2 h32), castToBool_boolBytes]
      simp only [Bool.not_true]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [offered_tailB2 f o remoteKey localKey payHash x rest _ hloc hpay (by simp only [MAX_OPS_PER_SCRIPT]; omega)
        (by simp only [MAX_STACK_SIZE]; omega)]
      rw [if_pos h32]
    · rw [decide_eq_false (fun h => h32 ((serialize_length_eq_32 _).1 h)), castToBool_boolBytes]
      simp only [Bool.not_false]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [offered_tailB1 f o remoteKey localKey payHash x rest _ hloc hpay (by simp only [MAX_OPS_PER_SCRIPT]; omega)
        (by simp only [MAX_STACK_SIZE]; omega)]
      rw [if_neg h32]

-- The offered script on a stack `x :: rest` of admissible size, in closed form.

set_option maxHeartbeats 1000000 in

private theorem offered_eval (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash x : Bytes) (rest : List Bytes)
    (hrev : revHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hn : rest.length + 3 ≤ MAX_STACK_SIZE) :
    evalScript f o (x :: rest) (offeredScript revHash remoteKey localKey payHash) =
      if o.hash160 x = revHash then sigResult o x rest
      else if MAX_STACK_SIZE < rest.length + 4 then none
      else if x.length = 32 then
        (if o.hash160 x = payHash then (if CsvPasses f o 1 then sigResult o remoteKey rest else none) else none)
      else (if CsvPasses f o 1 then msResult f o localKey remoteKey rest else none) := by
  simp only [MAX_STACK_SIZE] at hn
  unfold evalScript offeredScript State.initial
  -- OP_DUP
  rw [run, step_op_exec f o _ OP_DUP (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
  rw [execOp_dup]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_HASH160
  rw [run, step_op_exec f o _ OP_HASH160 (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
  rw [execOp_hash160]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- push revHash
  rw [run, step_push_exec f o _ revHash hrev allTrue_nil]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_EQUAL
  rw [run, step_op_exec f o _ OP_EQUAL (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
  rw [execOp_equal]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_IF
  rw [run, step_op_cond f o _ OP_IF (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
  rw [allTrue_nil, execOp_if_exec]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  by_cases hb : o.hash160 x = revHash
  · rw [decide_eq_true hb, castToBool_boolBytes]
    rw [offered_tailA f o remoteKey localKey payHash x rest _ hrem hloc hpay (by simp [MAX_OPS_PER_SCRIPT])
      (by simp only [MAX_STACK_SIZE]; omega)]
    rw [if_pos hb]
  · rw [decide_eq_false hb, castToBool_boolBytes]
    rw [offered_tailB f o remoteKey localKey payHash x rest _ hrem hloc hpay (by simp [MAX_OPS_PER_SCRIPT])
      (by simp only [MAX_STACK_SIZE]; omega)]
    rw [if_neg hb]

private theorem offered_eval_nil (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash : Bytes) :
    evalScript f o [] (offeredScript revHash remoteKey localKey payHash) = none := by
  unfold evalScript offeredScript State.initial
  rw [run, step_op_exec f o _ OP_DUP (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
  rw [execOp_dup]
  rfl

private theorem offered_eval_large (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash x : Bytes) (rest : List Bytes)
    (hrev : revHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hn : MAX_STACK_SIZE < rest.length + 3) :
    evalScript f o (x :: rest) (offeredScript revHash remoteKey localKey payHash) = none := by
  simp only [MAX_STACK_SIZE] at hn
  unfold evalScript offeredScript State.initial
  rw [run, step_op_exec f o _ OP_DUP (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
  rw [execOp_dup]
  dsimp only
  by_cases h1 : 1000 < rest.length + 2
  · rw [if_pos (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    rfl
  · rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    rw [run, step_op_exec f o _ OP_HASH160 (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
    rw [execOp_hash160]
    dsimp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    rw [run, step_push_exec f o _ revHash hrev allTrue_nil]
    rw [if_pos (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    rfl

/-- The `NULLDUMMY` test of `OP_CHECKMULTISIG` as a proposition on the dummy element. -/
private theorem nulldummy_iff (f : Flags) (d : Bytes) :
    ¬ (f.nulldummy && !d.isEmpty) = true ↔ (f.nulldummy = true → d = []) := by
  cases f.nulldummy
  · simp
  · cases d <;> simp

/-- A single true result of `sigResult`: the stack below was a lone signature, and it verified. -/
private theorem sigResult_one (o : Oracle) (pk : Bytes) (rest res : List Bytes)
    (hres : sigResult o pk rest = some res) (hlen : res.length = 1) (htop : topTrue res = true) :
    ∃ sig, rest = [sig] ∧ o.checkSig sig pk = some true := by
  cases rest with
  | nil => simp [sigResult] at hres
  | cons sig r =>
    dsimp only [sigResult] at hres
    cases hcs : o.checkSig sig pk with
    | none => rw [hcs] at hres; cases hres
    | some ok =>
      rw [hcs] at hres; simp only [Option.map_some, Option.some.injEq] at hres
      subst hres; simp only [List.length_cons] at hlen
      have hr : r = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hr
      simp only [topTrue, castToBool_boolBytes] at htop
      exact ⟨sig, rfl, by rw [hcs, htop]⟩

/-- A single true result of `msResult`: the stack below was two signatures and a dummy, the 2-of-2
check passed, and the dummy was admissible. -/
private theorem msResult_one (f : Flags) (o : Oracle) (k1 k2 : Bytes) (rest res : List Bytes)
    (hres : msResult f o k1 k2 rest = some res) (hlen : res.length = 1) (htop : topTrue res = true) :
    ∃ s1 s2 dummy, rest = [s1, s2, dummy] ∧ multisigLoop o [s1, s2] [k1, k2] = some true ∧
      (f.nulldummy = true → dummy = []) := by
  match rest with
  | [] => simp [msResult] at hres
  | [s1] => simp [msResult] at hres
  | [s1, s2] => simp [msResult] at hres
  | s1 :: s2 :: dummy :: r =>
    dsimp only [msResult] at hres
    cases hml : multisigLoop o [s1, s2] [k1, k2] with
    | none => rw [hml] at hres; cases hres
    | some ok =>
      rw [hml] at hres
      dsimp only at hres
      split at hres
      · cases hres
      · rename_i hd
        simp only [Option.some.injEq] at hres
        subst hres; simp only [List.length_cons] at hlen
        have hr : r = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hr
        simp only [topTrue, castToBool_boolBytes] at htop
        exact ⟨s1, s2, dummy, rfl, by rw [hml, htop], (nulldummy_iff f dummy).1 hd⟩

private theorem sigResult_true (o : Oracle) (pk sig : Bytes) (hcs : o.checkSig sig pk = some true) :
    ∃ res, sigResult o pk [sig] = some res ∧ res.length = 1 ∧ topTrue res = true := by
  dsimp only [sigResult]; rw [hcs]; exact ⟨_, rfl, rfl, rfl⟩

private theorem msResult_true (f : Flags) (o : Oracle) (k1 k2 s1 s2 d : Bytes)
    (hml : multisigLoop o [s1, s2] [k1, k2] = some true) (hd : f.nulldummy = true → d = []) :
    ∃ res, msResult f o k1 k2 [s1, s2, d] = some res ∧ res.length = 1 ∧ topTrue res = true := by
  dsimp only [msResult]; rw [hml]; dsimp only
  rw [if_neg ((nulldummy_iff f d).2 hd)]
  exact ⟨_, rfl, rfl, rfl⟩

private theorem ser_expiry_len (expiry : Int) (hd : expiry.natAbs < 2 ^ 32) :
    (serialize expiry).length ≤ MAX_SCRIPT_ELEMENT_SIZE :=
  Nat.le_trans (serialize_length expiry 4 (by simpa using hd)) (by decide)

-- Branch A (revocation) of the received script, from `OP_CHECKSIG` on.

set_option maxHeartbeats 1000000 in

private theorem received_tailA (f : Flags) (o : Oracle) (remoteKey localKey payHash x : Bytes) (expiry : Int)
    (rest : List Bytes) (k : Nat)
    (hrem : remoteKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hloc : localKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hpay : payHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hd : expiry.natAbs < 2 ^ 32) (hk : k + 25 ≤ MAX_OPS_PER_SCRIPT)
    (hn : rest.length + 1 ≤ MAX_STACK_SIZE) :
    (run f o ⟨x :: rest, [], [true], k⟩
      [.op OP_CHECKSIG,
       .op OP_ELSE, .push remoteKey, .op OP_SWAP, .op OP_SIZE, numInstr 32, .op OP_EQUAL,
       .op OP_IF, .op OP_HASH160, .push payHash, .op OP_EQUALVERIFY, numInstr 2, .op OP_SWAP, .push localKey,
         numInstr 2, .op OP_CHECKMULTISIG,
       .op OP_ELSE, .op OP_DROP, numInstr expiry, .op OP_CHECKLOCKTIMEVERIFY, .op OP_DROP, .op OP_CHECKSIG,
       .op OP_ENDIF,
       numInstr 1, .op OP_CHECKSEQUENCEVERIFY, .op OP_DROP,
       .op OP_ENDIF]).map State.stack = sigResult o x rest := by
  have hser := ser_expiry_len expiry hd
  simp only [MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT] at hn hk
  -- OP_CHECKSIG
  rw [run, step_op_exec f o _ OP_CHECKSIG (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
  rw [execOp_checksig]
  cases rest with
  | nil => rfl
  | cons sig r =>
    dsimp only [sigResult]
    cases o.checkSig sig x with
    | none => rfl
    | some ok =>
      dsimp only
      simp only [List.length_cons] at hn
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- OP_ELSE
      rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
      rw [execOp_else]
      dsimp only
      simp only [Bool.not_true]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [run_push_skip f o _ _ _ _ remoteKey _ hrem allTrue_f (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_SWAP _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_f (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_SIZE _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_f (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_num_skip f o _ _ _ _ 32 _ ser32_len allTrue_f (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_EQUAL _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_f (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      -- OP_IF (not executing)
      rw [run, step_op_cond f o _ OP_IF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
      rw [allTrue_f, execOp_if_skip]
      dsimp only
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [run_op_skip f o _ _ _ _ OP_HASH160 _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ff (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_push_skip f o _ _ _ _ payHash _ hpay allTrue_ff (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_EQUALVERIFY _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ff (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_num_skip f o _ _ _ _ 2 _ ser2_len allTrue_ff (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_SWAP _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ff (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_push_skip f o _ _ _ _ localKey _ hloc allTrue_ff (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_num_skip f o _ _ _ _ 2 _ ser2_len allTrue_ff (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_CHECKMULTISIG _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ff (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      -- OP_ELSE (inner)
      rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
      rw [execOp_else]
      dsimp only
      simp only [Bool.not_false]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [run_op_skip f o _ _ _ _ OP_DROP _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tf (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_num_skip f o _ _ _ _ expiry _ hser allTrue_tf (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_CHECKLOCKTIMEVERIFY _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tf (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_DROP _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tf (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_CHECKSIG _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tf (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      -- OP_ENDIF, OP_ENDIF
      rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
      rw [execOp_endif]
      dsimp only
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- 1 OP_CHECKSEQUENCEVERIFY OP_DROP (skipped)
      rw [run_num_skip f o _ _ _ _ 1 _ ser1_len allTrue_f (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_CHECKSEQUENCEVERIFY _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_f (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run_op_skip f o _ _ _ _ OP_DROP _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_f (by decide)
        (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
      rw [execOp_endif]
      dsimp only
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [run_nil]
      rfl

-- Branch B1 (success, preimage and 2-of-2) of the received script, from `OP_HASH160` on.

set_option maxHeartbeats 1000000 in

private theorem received_tailB1 (f : Flags) (o : Oracle) (remoteKey localKey payHash x : Bytes) (expiry : Int)
    (rest : List Bytes) (k : Nat)
    (hloc : localKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) (hk : k + 25 ≤ MAX_OPS_PER_SCRIPT) (hn : rest.length + 4 ≤ MAX_STACK_SIZE) :
    (run f o ⟨x :: remoteKey :: rest, [], [true, true], k⟩
      [.op OP_HASH160, .push payHash, .op OP_EQUALVERIFY, numInstr 2, .op OP_SWAP, .push localKey,
         numInstr 2, .op OP_CHECKMULTISIG,
       .op OP_ELSE, .op OP_DROP, numInstr expiry, .op OP_CHECKLOCKTIMEVERIFY, .op OP_DROP, .op OP_CHECKSIG,
       .op OP_ENDIF,
       numInstr 1, .op OP_CHECKSEQUENCEVERIFY, .op OP_DROP,
       .op OP_ENDIF]).map State.stack =
      if o.hash160 x = payHash then (if CsvPasses f o 1 then msResult f o localKey remoteKey rest else none) else none := by
  have hser := ser_expiry_len expiry hd
  simp only [MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT] at hn hk
  -- OP_HASH160
  rw [run, step_op_exec f o _ OP_HASH160 (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tt]
  rw [execOp_hash160]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- push payHash
  rw [run, step_push_exec f o _ payHash hpay allTrue_tt]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_EQUALVERIFY
  rw [run, step_op_exec f o _ OP_EQUALVERIFY (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tt]
  rw [execOp_equalverify]
  dsimp only
  by_cases hp : o.hash160 x = payHash
  · rw [if_pos (decide_eq_true hp), if_pos hp]
    dsimp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- 2
    rw [run, numInstr_exec f o _ 2 ser2_len allTrue_tt]
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_SWAP
    rw [run, step_op_exec f o _ OP_SWAP (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tt]
    rw [execOp_swap]
    dsimp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- push localKey
    rw [run, step_push_exec f o _ localKey hloc allTrue_tt]
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- 2
    rw [run, numInstr_exec f o _ 2 ser2_len allTrue_tt]
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_CHECKMULTISIG
    rw [run, step_op_exec f o _ OP_CHECKMULTISIG (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tt]
    dsimp only
    rw [cms_two f o localKey remoteKey rest [] [true, true] _ (by simp only [MAX_OPS_PER_SCRIPT]; omega)]
    match rest with
    | [] => simp only [msResult, ite_self]; rfl
    | [s1] => simp only [msResult, ite_self]; rfl
    | [s1, s2] => simp only [msResult, ite_self]; rfl
    | s1 :: s2 :: dummy :: r =>
      dsimp only [msResult]
      simp only [List.length_cons] at hn
      cases multisigLoop o [s1, s2] [localKey, remoteKey] with
      | none => rw [ite_self]; rfl
      | some ok =>
        dsimp only
        by_cases hdm : (f.nulldummy && !dummy.isEmpty) = true
        · rw [if_pos hdm, if_pos hdm, ite_self]; rfl
        · rw [if_neg hdm, if_neg hdm]
          dsimp only
          rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          dsimp only
          -- OP_ELSE
          rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
          rw [execOp_else]
          dsimp only
          simp only [Bool.not_true]
          rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          dsimp only
          rw [run_op_skip f o _ _ _ _ OP_DROP _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ft (by decide)
            (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          rw [run_num_skip f o _ _ _ _ expiry _ hser allTrue_ft (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          rw [run_op_skip f o _ _ _ _ OP_CHECKLOCKTIMEVERIFY _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ft (by decide)
            (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          rw [run_op_skip f o _ _ _ _ OP_DROP _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ft (by decide)
            (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          rw [run_op_skip f o _ _ _ _ OP_CHECKSIG _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ft (by decide)
            (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          -- inner OP_ENDIF
          rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
          rw [execOp_endif]
          dsimp only
          rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          dsimp only
          -- 1 OP_CHECKSEQUENCEVERIFY OP_DROP
          rw [run, numInstr_exec f o _ 1 ser1_len allTrue_t]
          rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          dsimp only
          rw [run, step_op_exec f o _ OP_CHECKSEQUENCEVERIFY (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
          rw [BitcoinToLocal.csv_step f o _ 1 _ rfl (by decide)]
          by_cases hc1 : CsvPasses f o 1
          · rw [if_pos hc1, if_pos hc1]
            dsimp only
            rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
            dsimp only
            rw [run, step_op_exec f o _ OP_DROP (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
            rw [execOp_drop]
            dsimp only
            rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
            dsimp only
            -- outer OP_ENDIF
            rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
            rw [execOp_endif]
            dsimp only
            rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
            dsimp only
            rw [run_nil]
            rfl
          · rw [if_neg hc1, if_neg hc1]
            rfl
  · rw [if_neg (by rw [decide_eq_false hp]; decide), if_neg hp]
    rfl

-- Branch B2 (timeout) of the received script, from `OP_HASH160` on.

set_option maxHeartbeats 1000000 in

private theorem received_tailB2 (f : Flags) (o : Oracle) (remoteKey localKey payHash x : Bytes) (expiry : Int)
    (rest : List Bytes) (k : Nat)
    (hloc : localKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) (hk : k + 25 ≤ MAX_OPS_PER_SCRIPT) (hn : rest.length + 3 ≤ MAX_STACK_SIZE) :
    (run f o ⟨x :: remoteKey :: rest, [], [false, true], k⟩
      [.op OP_HASH160, .push payHash, .op OP_EQUALVERIFY, numInstr 2, .op OP_SWAP, .push localKey,
         numInstr 2, .op OP_CHECKMULTISIG,
       .op OP_ELSE, .op OP_DROP, numInstr expiry, .op OP_CHECKLOCKTIMEVERIFY, .op OP_DROP, .op OP_CHECKSIG,
       .op OP_ENDIF,
       numInstr 1, .op OP_CHECKSEQUENCEVERIFY, .op OP_DROP,
       .op OP_ENDIF]).map State.stack =
      if BitcoinHtlc.CltvPasses f o expiry then (if CsvPasses f o 1 then sigResult o remoteKey rest else none) else none := by
  have hser := ser_expiry_len expiry hd
  simp only [MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT] at hn hk
  rw [run_op_skip f o _ _ _ _ OP_HASH160 _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ft (by decide)
    (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rw [run_push_skip f o _ _ _ _ payHash _ hpay allTrue_ft (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rw [run_op_skip f o _ _ _ _ OP_EQUALVERIFY _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ft (by decide)
    (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rw [run_num_skip f o _ _ _ _ 2 _ ser2_len allTrue_ft (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rw [run_op_skip f o _ _ _ _ OP_SWAP _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ft (by decide)
    (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rw [run_push_skip f o _ _ _ _ localKey _ hloc allTrue_ft (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rw [run_num_skip f o _ _ _ _ 2 _ ser2_len allTrue_ft (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rw [run_op_skip f o _ _ _ _ OP_CHECKMULTISIG _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_ft (by decide)
    (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  -- OP_ELSE
  rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
  rw [execOp_else]
  dsimp only
  simp only [Bool.not_false]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_DROP
  rw [run, step_op_exec f o _ OP_DROP (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tt]
  rw [execOp_drop]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- expiry
  rw [run, numInstr_exec f o _ expiry hser allTrue_tt]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_CHECKLOCKTIMEVERIFY
  rw [run, step_op_exec f o _ OP_CHECKLOCKTIMEVERIFY (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tt]
  rw [BitcoinHtlc.cltv_step f o _ expiry (remoteKey :: rest) rfl hd]
  by_cases hc : BitcoinHtlc.CltvPasses f o expiry
  · rw [if_pos hc, if_pos hc]
    dsimp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_DROP
    rw [run, step_op_exec f o _ OP_DROP (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tt]
    rw [execOp_drop]
    dsimp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_CHECKSIG
    rw [run, step_op_exec f o _ OP_CHECKSIG (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_tt]
    rw [execOp_checksig]
    cases rest with
    | nil => rw [show sigResult o remoteKey [] = none from rfl, ite_self]; rfl
    | cons sig r =>
      dsimp only [sigResult]
      cases o.checkSig sig remoteKey with
      | none => rw [show Option.map (fun ok => boolBytes ok :: r) (none : Option Bool) = none from rfl, ite_self]; rfl
      | some ok =>
        dsimp only
        simp only [List.length_cons] at hn
        rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        dsimp only
        -- inner OP_ENDIF
        rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
        rw [execOp_endif]
        dsimp only
        rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        dsimp only
        -- 1 OP_CHECKSEQUENCEVERIFY OP_DROP
        rw [run, numInstr_exec f o _ 1 ser1_len allTrue_t]
        rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
        dsimp only
        rw [run, step_op_exec f o _ OP_CHECKSEQUENCEVERIFY (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
        rw [BitcoinToLocal.csv_step f o _ 1 _ rfl (by decide)]
        by_cases hc1 : CsvPasses f o 1
        · rw [if_pos hc1, if_pos hc1]
          dsimp only
          rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          dsimp only
          rw [run, step_op_exec f o _ OP_DROP (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
          rw [execOp_drop]
          dsimp only
          rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          dsimp only
          -- outer OP_ENDIF
          rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
          rw [execOp_endif]
          dsimp only
          rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
          dsimp only
          rw [run_nil]
          rfl
        · rw [if_neg hc1, if_neg hc1]
          rfl
  · rw [if_neg hc, if_neg hc]
    rfl

-- Branch B (not the revocation key) of the received script, from the (skipped) `OP_CHECKSIG` on.

set_option maxHeartbeats 1000000 in

private theorem received_tailB (f : Flags) (o : Oracle) (remoteKey localKey payHash x : Bytes) (expiry : Int)
    (rest : List Bytes) (k : Nat)
    (hrem : remoteKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hloc : localKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hpay : payHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hd : expiry.natAbs < 2 ^ 32) (hk : k + 35 ≤ MAX_OPS_PER_SCRIPT)
    (hn : rest.length + 3 ≤ MAX_STACK_SIZE) :
    (run f o ⟨x :: rest, [], [false], k⟩
      [.op OP_CHECKSIG,
       .op OP_ELSE, .push remoteKey, .op OP_SWAP, .op OP_SIZE, numInstr 32, .op OP_EQUAL,
       .op OP_IF, .op OP_HASH160, .push payHash, .op OP_EQUALVERIFY, numInstr 2, .op OP_SWAP, .push localKey,
         numInstr 2, .op OP_CHECKMULTISIG,
       .op OP_ELSE, .op OP_DROP, numInstr expiry, .op OP_CHECKLOCKTIMEVERIFY, .op OP_DROP, .op OP_CHECKSIG,
       .op OP_ENDIF,
       numInstr 1, .op OP_CHECKSEQUENCEVERIFY, .op OP_DROP,
       .op OP_ENDIF]).map State.stack =
      if MAX_STACK_SIZE < rest.length + 4 then none
      else if x.length = 32 then
        (if o.hash160 x = payHash then (if CsvPasses f o 1 then msResult f o localKey remoteKey rest else none) else none)
      else (if BitcoinHtlc.CltvPasses f o expiry then (if CsvPasses f o 1 then sigResult o remoteKey rest else none) else none) := by
  simp only [MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT] at hn hk
  rw [run_op_skip f o _ _ _ _ OP_CHECKSIG _ (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_f (by decide)
    (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  -- OP_ELSE
  rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
  rw [execOp_else]
  dsimp only
  simp only [Bool.not_false]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- push remoteKey
  rw [run, step_push_exec f o _ remoteKey hrem allTrue_t]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_SWAP
  rw [run, step_op_exec f o _ OP_SWAP (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
  rw [execOp_swap]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_SIZE
  rw [run, step_op_exec f o _ OP_SIZE (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
  rw [execOp_size]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- 32
  rw [run, numInstr_exec f o _ 32 ser32_len allTrue_t]
  by_cases hg : MAX_STACK_SIZE < rest.length + 4
  · rw [if_pos (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE] at hg ⊢; omega), if_pos hg]
    rfl
  · rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE] at hg ⊢; omega), if_neg hg]
    dsimp only
    simp only [MAX_STACK_SIZE] at hg
    -- OP_EQUAL
    rw [run, step_op_exec f o _ OP_EQUAL (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) allTrue_t]
    rw [execOp_equal]
    dsimp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_IF
    rw [run, step_op_cond f o _ OP_IF (by decide) (by simp only [MAX_OPS_PER_SCRIPT]; omega) (by decide) (by decide)]
    rw [allTrue_t, execOp_if_exec]
    dsimp only
    by_cases h32 : x.length = 32
    · rw [decide_eq_true ((serialize_length_eq_32 _).2 h32), castToBool_boolBytes]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [received_tailB1 f o remoteKey localKey payHash x expiry rest _ hloc hpay hd (by simp only [MAX_OPS_PER_SCRIPT]; omega)
        (by simp only [MAX_STACK_SIZE]; omega)]
      rw [if_pos h32]
    · rw [decide_eq_false (fun h => h32 ((serialize_length_eq_32 _).1 h)), castToBool_boolBytes]
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [received_tailB2 f o remoteKey localKey payHash x expiry rest _ hloc hpay hd (by simp only [MAX_OPS_PER_SCRIPT]; omega)
        (by simp only [MAX_STACK_SIZE]; omega)]
      rw [if_neg h32]

-- The received script on a stack `x :: rest` of admissible size, in closed form.

set_option maxHeartbeats 1000000 in

private theorem received_eval (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash x : Bytes) (expiry : Int)
    (rest : List Bytes)
    (hrev : revHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) (hn : rest.length + 3 ≤ MAX_STACK_SIZE) :
    evalScript f o (x :: rest) (receivedScript revHash remoteKey localKey payHash expiry) =
      if o.hash160 x = revHash then sigResult o x rest
      else if MAX_STACK_SIZE < rest.length + 4 then none
      else if x.length = 32 then
        (if o.hash160 x = payHash then (if CsvPasses f o 1 then msResult f o localKey remoteKey rest else none) else none)
      else (if BitcoinHtlc.CltvPasses f o expiry then (if CsvPasses f o 1 then sigResult o remoteKey rest else none) else none) := by
  simp only [MAX_STACK_SIZE] at hn
  unfold evalScript receivedScript State.initial
  -- OP_DUP
  rw [run, step_op_exec f o _ OP_DUP (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
  rw [execOp_dup]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_HASH160
  rw [run, step_op_exec f o _ OP_HASH160 (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
  rw [execOp_hash160]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- push revHash
  rw [run, step_push_exec f o _ revHash hrev allTrue_nil]
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_EQUAL
  rw [run, step_op_exec f o _ OP_EQUAL (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
  rw [execOp_equal]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  -- OP_IF
  rw [run, step_op_cond f o _ OP_IF (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
  rw [allTrue_nil, execOp_if_exec]
  dsimp only
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  by_cases hb : o.hash160 x = revHash
  · rw [decide_eq_true hb, castToBool_boolBytes]
    rw [received_tailA f o remoteKey localKey payHash x expiry rest _ hrem hloc hpay hd (by simp [MAX_OPS_PER_SCRIPT])
      (by simp only [MAX_STACK_SIZE]; omega)]
    rw [if_pos hb]
  · rw [decide_eq_false hb, castToBool_boolBytes]
    rw [received_tailB f o remoteKey localKey payHash x expiry rest _ hrem hloc hpay hd (by simp [MAX_OPS_PER_SCRIPT])
      (by simp only [MAX_STACK_SIZE]; omega)]
    rw [if_neg hb]

private theorem received_eval_nil (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash : Bytes) (expiry : Int) :
    evalScript f o [] (receivedScript revHash remoteKey localKey payHash expiry) = none := by
  unfold evalScript receivedScript State.initial
  rw [run, step_op_exec f o _ OP_DUP (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
  rw [execOp_dup]
  rfl

private theorem received_eval_large (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash x : Bytes) (expiry : Int)
    (rest : List Bytes) (hrev : revHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hn : MAX_STACK_SIZE < rest.length + 3) :
    evalScript f o (x :: rest) (receivedScript revHash remoteKey localKey payHash expiry) = none := by
  simp only [MAX_STACK_SIZE] at hn
  unfold evalScript receivedScript State.initial
  rw [run, step_op_exec f o _ OP_DUP (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
  rw [execOp_dup]
  dsimp only
  by_cases h1 : 1000 < rest.length + 2
  · rw [if_pos (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    rfl
  · rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    rw [run, step_op_exec f o _ OP_HASH160 (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
    rw [execOp_hash160]
    dsimp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    rw [run, step_push_exec f o _ revHash hrev allTrue_nil]
    rw [if_pos (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    rfl

private theorem getOp_op (c : BitcoinScript.Byte) (rest : Bytes) (hc : OP_PUSHDATA4 < c.toNat) :
    getOp (c :: rest) = some (.op c, rest) := by
  unfold getOp
  dsimp only
  rw [if_neg (Nat.not_le.mpr hc)]

private theorem leBytes_len (k n : Nat) : (BitcoinSer.leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [BitcoinSer.leBytes, ih]

private theorem leVal_leBytes2 (n : Nat) (h : n < 65536) : BitcoinSer.leVal (BitcoinSer.leBytes 2 n) = n := by
  simp [BitcoinSer.leBytes, BitcoinSer.leVal, BitVec.toNat_ofNat]; omega

private theorem getOp_pushBytes (d rest : Bytes) (hd : d.length ≤ MAX_SCRIPT_ELEMENT_SIZE) :
    getOp (pushBytes d ++ rest) = some (.push d, rest) := by
  unfold MAX_SCRIPT_ELEMENT_SIZE at hd
  have hlen : ¬ (d.length + rest.length < d.length) := by omega
  unfold pushBytes OP_PUSHDATA1 OP_PUSHDATA2 OP_PUSHDATA4
  by_cases h1 : d.length < 76
  · rw [if_pos h1]
    simp only [List.cons_append, getOp, OP_PUSHDATA1, OP_PUSHDATA2, OP_PUSHDATA4, BitVec.toNat_ofNat, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp [h1, hlen]
    omega
  · rw [if_neg h1]
    by_cases h2 : d.length ≤ 0xff
    · rw [if_pos h2]
      simp only [List.cons_append, List.nil_append, getOp, OP_PUSHDATA1, OP_PUSHDATA2, OP_PUSHDATA4,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      rw [Nat.mod_eq_of_lt (by omega)]
      simp [hlen]
    · rw [if_neg h2, if_pos (by omega)]
      have hl : (BitcoinSer.leBytes 2 d.length ++ (d ++ rest)).length = 2 + (d.length + rest.length) := by
        simp [leBytes_len]
      simp only [List.cons_append, getOp, OP_PUSHDATA1, OP_PUSHDATA2, OP_PUSHDATA4, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, List.append_assoc]
      simp only [show (77:Nat) ≤ 78 from by omega, show ¬ ((77:Nat) < 76) from by omega, show (77:Nat) ≠ 76 from by omega,
        if_true, if_false, ite_true, ite_false, ne_eq, not_false_eq_true, not_true_eq_false]
      rw [if_neg (by rw [hl]; omega),
        List.take_left' (leBytes_len 2 _), List.drop_left' (leBytes_len 2 _), leVal_leBytes2 _ (by omega)]
      simp [hlen]

private theorem pushBytes_length_le (d : Bytes) : (pushBytes d).length ≤ d.length + 5 := by
  unfold pushBytes
  split
  · simp
  · split
    · simp
    · split
      · simp [leBytes_len]; omega
      · simp [leBytes_len]; omega

private theorem pushBytes_length_pos (d : Bytes) : 1 ≤ (pushBytes d).length := by
  unfold pushBytes
  split
  · simp
  · split
    · simp
    · split
      · simp
      · simp

private theorem parseScriptAux_step (fuel : Nat) (s r : Bytes) (i : Instr) (h : getOp s = some (i, r)) :
    parseScriptAux (fuel + 1) s = (parseScriptAux fuel r).map (i :: ·) := by
  cases s with
  | nil => simp [getOp] at h
  | cons b bs =>
    simp only [parseScriptAux, h]
    cases parseScriptAux fuel r <;> rfl

private theorem parseScriptAux_nil (fuel : Nat) : parseScriptAux fuel [] = some [] := by
  cases fuel <;> rfl

private theorem getOp_numBytes (n : Int) (rest : Bytes) (hn : (serialize n).length ≤ MAX_SCRIPT_ELEMENT_SIZE) :
    getOp (numBytes n ++ rest) = some (numInstr n, rest) := by
  unfold numBytes numInstr
  split
  · rename_i h
    simp only [List.cons_append, List.nil_append]
    apply getOp_op
    have h17 : n = -1 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨
        n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by omega
    rcases h17 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact getOp_pushBytes _ _ hn

private theorem numBytes_length_le (n : Int) : (numBytes n).length ≤ (serialize n).length + 5 := by
  unfold numBytes
  split
  · simp
  · exact pushBytes_length_le _

private theorem numBytes_length_pos (n : Int) : 1 ≤ (numBytes n).length := by
  unfold numBytes
  split
  · simp
  · exact pushBytes_length_pos _

private theorem ser1_eq : (serialize 1).length = 1 := by rw [serialize_one]; rfl

private theorem ser16_eq : (serialize 16).length = 1 := by rw [serialize_16]; rfl

private theorem toRemoteBytes_length (remoteKey : Bytes) (hrem : remoteKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) :
    (toRemoteBytes remoteKey).length ≤ MAX_SCRIPT_SIZE := by
  have h1 := pushBytes_length_le remoteKey
  have h2 := numBytes_length_le 1
  have h3 := ser1_eq
  simp only [toRemoteBytes, List.length_append, List.length_cons, List.length_nil, MAX_SCRIPT_SIZE,
    MAX_SCRIPT_ELEMENT_SIZE] at *
  omega

private theorem anchorBytes_length (fundingKey : Bytes) (hfk : fundingKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) :
    (anchorBytes fundingKey).length ≤ MAX_SCRIPT_SIZE := by
  have h1 := pushBytes_length_le fundingKey
  have h2 := numBytes_length_le 16
  have h3 := ser16_eq
  simp only [anchorBytes, List.length_append, List.length_cons, List.length_nil, MAX_SCRIPT_SIZE,
    MAX_SCRIPT_ELEMENT_SIZE] at *
  omega

private theorem offeredBytes_length (revHash remoteKey localKey payHash : Bytes)
    (hrev : revHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE) :
    (offeredBytes revHash remoteKey localKey payHash).length ≤ MAX_SCRIPT_SIZE := by
  have h1 := pushBytes_length_le revHash
  have h2 := pushBytes_length_le remoteKey
  have h3 := pushBytes_length_le localKey
  have h4 := pushBytes_length_le payHash
  have h5 := numBytes_length_le 32
  have h6 := numBytes_length_le 2
  have h7 : (serialize 32).length = 1 := by rw [serialize_32]; rfl
  have h8 : (serialize 2).length = 1 := by rw [serialize_two]; rfl
  have h9 := numBytes_length_le 1
  have h10 := ser1_eq
  simp only [offeredBytes, List.length_append, List.length_cons, List.length_nil, MAX_SCRIPT_SIZE,
    MAX_SCRIPT_ELEMENT_SIZE] at *
  omega

private theorem receivedBytes_length (revHash remoteKey localKey payHash : Bytes) (expiry : Int)
    (hrev : revHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) :
    (receivedBytes revHash remoteKey localKey payHash expiry).length ≤ MAX_SCRIPT_SIZE := by
  have h1 := pushBytes_length_le revHash
  have h2 := pushBytes_length_le remoteKey
  have h3 := pushBytes_length_le localKey
  have h4 := pushBytes_length_le payHash
  have h5 := numBytes_length_le 32
  have h6 := numBytes_length_le 2
  have h7 : (serialize 32).length = 1 := by rw [serialize_32]; rfl
  have h8 : (serialize 2).length = 1 := by rw [serialize_two]; rfl
  have h9 := numBytes_length_le expiry
  have h10 := serialize_length expiry 4 (by simpa using hd)
  have h11 := numBytes_length_le 1
  have h12 := ser1_eq
  simp only [receivedBytes, List.length_append, List.length_cons, List.length_nil, MAX_SCRIPT_SIZE,
    MAX_SCRIPT_ELEMENT_SIZE] at *
  omega

/-- The witness-element size test of `ExecuteWitnessScript`, as a proposition on the witness. -/
private theorem any_size_iff (ws : List Bytes) :
    ¬ (ws.reverse.any fun e => decide (MAX_SCRIPT_ELEMENT_SIZE < e.length)) = true ↔
      ∀ e ∈ ws, e.length ≤ MAX_SCRIPT_ELEMENT_SIZE := by
  simp only [List.any_eq_true, List.mem_reverse, decide_eq_true_eq, not_exists, not_and, Nat.not_lt]

/-- `ExecuteWitnessScript` (version 0) on a script whose byte form parses and whose instruction form
has a `spends_iff` characterization. -/
private theorem executeWitnessScriptV0_iff (c : Ctx) (ws : List Bytes) (bytes : Bytes) (script : Script)
    (P : List Bytes → Prop)
    (hsz : bytes.length ≤ MAX_SCRIPT_SIZE) (hparse : parseScript bytes = some script)
    (hiff : ∀ st, (∃ res, evalScript (scriptFlagsOf c.flags)
        (legacyOracle (sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 bytes) st script = some res ∧
        res.length = 1 ∧ topTrue res = true) ↔ P st) :
    executeWitnessScriptV0 c ws.reverse bytes = true ↔
      (∀ e ∈ ws, e.length ≤ MAX_SCRIPT_ELEMENT_SIZE) ∧ P ws.reverse := by
  unfold executeWitnessScriptV0 evalBytes
  rw [if_neg (Nat.not_lt.mpr hsz), hparse]
  constructor
  · intro h
    split at h
    · cases h
    · rename_i hany
      refine ⟨(any_size_iff ws).1 hany, ?_⟩
      dsimp only at h
      cases hev : evalScript (scriptFlagsOf c.flags)
          (legacyOracle (sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 bytes) ws.reverse script with
      | none => rw [hev] at h; cases h
      | some res =>
        rw [hev] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact (hiff ws.reverse).1 ⟨res, hev, h.1, h.2⟩
  · rintro ⟨hsz', hsc⟩
    rw [if_neg ((any_size_iff ws).2 hsz')]
    obtain ⟨res, hev, hl, ht⟩ := (hiff ws.reverse).2 hsc
    dsimp only
    rw [hev]
    simp [hl, ht]

/-- Under the consensus signature flags (`sigFlagsOf`: neither `STRICTENC` nor
`WITNESS_PUBKEYTYPE`), every public key passes the encoding check. -/
private theorem checkPubKeyEncoding_consensus (fl : BitcoinActivation.ScriptFlags) (v : SigVersion) (pk : Bytes) :
    checkPubKeyEncoding (sigFlagsOf fl) v pk = true := by
  unfold checkPubKeyEncoding sigFlagsOf
  simp

/-- **The anyone-can-spend anchor path, concretely.** With the `CHECKSEQUENCEVERIFY` flag on, the
witness `<>` (the empty signature, which the checker rejects cleanly) followed by the anchor script
verifies exactly when the script hash is a true value and the spending transaction's
`CheckSequence(16)` holds. -/
theorem solution (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (fundingKey : Bytes)
    (hfk : fundingKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.verifyScript tap c []
        (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fundingKey)))
        [[], BitcoinAnchors.anchorBytes fundingKey] = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fundingKey)) = true ∧
      BitcoinSig.checkSequence c.tx c.nIn 16 = true := by
  rw [show [[], anchorBytes fundingKey] = [[]] ++ [anchorBytes fundingKey] from rfl,
    BitcoinAnchors.anchor_p2wsh_spend tap c hf fundingKey [[]] hfk]
  apply and_congr_right
  intro _
  have hempty : (legacyOracle (sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 (anchorBytes fundingKey)).checkSig [] fundingKey =
      some false :=
    BitcoinSig.checkSig_empty (sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 (anchorBytes fundingKey) fundingKey
      (checkPubKeyEncoding_consensus c.flags .witnessV0 fundingKey)
  have hcsv' : (scriptFlagsOf c.flags).csv = true := hcsv
  have hconc := BitcoinToLocal.csv_concrete (scriptFlagsOf c.flags) (sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
    (anchorBytes fundingKey) 16 hcsv' (by decide) (by decide)
  constructor
  · rintro ⟨-, ⟨sig, hsig, h⟩⟩
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons.injEq, and_true] at hsig
    subst hsig
    rcases h with h | ⟨-, h⟩
    · rw [hempty] at h; cases h
    · exact hconc.1 h
  · intro h
    exact ⟨by simp, [], rfl, Or.inr ⟨hempty, hconc.2 h⟩⟩
