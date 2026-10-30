-- Prove2me | solution 1 for BitcoinFunding.parseScript_funding
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T20:22:07.980113+00:00
-- url     : https://prove2.me/submissions/3a1171c1-6495-479a-81eb-45b105ca10dd

import Definitions.Def_BitcoinFunding
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinVerify_p2wsh_correct
import Theorems.Thm_BitcoinHtlc_multisig_two

open BitcoinFunding BitcoinHtlc
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

/-- `OP_CHECKLOCKTIMEVERIFY` on a stack whose top is the serialization of a 5-byte number. -/
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

/-- `CScript`'s byte form of the offered script parses to its instruction form. -/
private theorem any_size_iff (ws : List Bytes) :
    ¬ (ws.reverse.any fun e => decide (MAX_SCRIPT_ELEMENT_SIZE < e.length)) = true ↔
      ∀ e ∈ ws, e.length ≤ MAX_SCRIPT_ELEMENT_SIZE := by
  simp only [List.any_eq_true, List.mem_reverse, decide_eq_true_eq, not_exists, not_and, Nat.not_lt]

private theorem allTrue_nil' : allTrue [] = true := rfl

/-- The result of the funding script on a stack: the 2-of-2 check on the three top elements. -/
private def fundResult (f : Flags) (o : Oracle) (k1 k2 : Bytes) : List Bytes → Option (List Bytes)
  | s2 :: s1 :: dummy :: rest =>
    match multisigLoop o [s2, s1] [k2, k1] with
    | none => none
    | some ok => if f.nulldummy && !dummy.isEmpty then none else some (boolBytes ok :: rest)
  | _ => none

/-- The funding script on any stack of admissible size. -/
private theorem funding_run (f : Flags) (o : Oracle) (k1 k2 : Bytes) (st : List Bytes)
    (h1 : k1.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (h2 : k2.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hst : st.length + 4 ≤ MAX_STACK_SIZE) :
    evalScript f o st (fundingScript k1 k2) = fundResult f o k1 k2 st := by
  have hser : (serialize 2).length ≤ MAX_SCRIPT_ELEMENT_SIZE := by rw [serialize_two]; decide
  simp only [MAX_STACK_SIZE] at hst
  unfold evalScript fundingScript State.initial
  rw [run, numInstr_exec f o _ 2 hser allTrue_nil']
  rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  rw [run, step_push_exec f o _ k1 h1 allTrue_nil']
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  rw [run, step_push_exec f o _ k2 h2 allTrue_nil']
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  rw [run, numInstr_exec f o _ 2 hser allTrue_nil']
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  rw [run, step_op_exec f o _ OP_CHECKMULTISIG (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil']
  rw [cms_two f o k2 k1 st [] [] 1 (by simp [MAX_OPS_PER_SCRIPT])]
  match st with
  | [] => rfl
  | [a] => rfl
  | [a, b] => rfl
  | s2 :: s1 :: dummy :: rest =>
    simp only [fundResult]
    cases multisigLoop o [s2, s1] [k2, k1] with
    | none => rfl
    | some ok =>
      dsimp only
      by_cases hn : (f.nulldummy && !dummy.isEmpty) = true
      · simp only [hn, ite_true]; rfl
      · rw [if_neg hn]
        dsimp only
        simp only [List.length_cons, List.length_nil] at hst ⊢
        rw [if_neg (by simp only [MAX_STACK_SIZE]; omega)]
        simp [run, hn]

private theorem funding_large (f : Flags) (o : Oracle) (k1 k2 : Bytes) (st : List Bytes)
    (h1 : k1.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (h2 : k2.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hst : MAX_STACK_SIZE < st.length + 4) :
    evalScript f o st (fundingScript k1 k2) = none := by
  have hser : (serialize 2).length ≤ MAX_SCRIPT_ELEMENT_SIZE := by rw [serialize_two]; decide
  simp only [MAX_STACK_SIZE] at hst
  unfold evalScript fundingScript State.initial
  rw [run, numInstr_exec f o _ 2 hser allTrue_nil']
  by_cases c1 : 1000 < st.length + 1
  · rw [if_pos (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]; rfl
  rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  rw [run, step_push_exec f o _ k1 h1 allTrue_nil']
  by_cases c2 : 1000 < st.length + 2
  · rw [if_pos (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]; rfl
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  rw [run, step_push_exec f o _ k2 h2 allTrue_nil']
  by_cases c3 : 1000 < st.length + 3
  · rw [if_pos (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]; rfl
  rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  rw [run, numInstr_exec f o _ 2 hser allTrue_nil']
  rw [if_pos (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
  rfl

/-- `CScript`'s byte form of the funding script parses to its instruction form. -/
theorem solution (pubkey1 pubkey2 : Bytes)
    (h1 : pubkey1.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (h2 : pubkey2.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinSig.parseScript (BitcoinFunding.fundingBytes pubkey1 pubkey2) = some (BitcoinFunding.fundingScript pubkey1 pubkey2) := by
  have hser : (serialize 2).length ≤ MAX_SCRIPT_ELEMENT_SIZE := by rw [serialize_two]; decide
  unfold parseScript
  have hlen : ∃ m, (fundingBytes pubkey1 pubkey2).length = m + 5 := by
    refine ⟨(fundingBytes pubkey1 pubkey2).length - 5, ?_⟩
    have := pushBytes_length_pos pubkey1
    have := pushBytes_length_pos pubkey2
    have := numBytes_length_pos 2
    simp only [fundingBytes, List.length_append, List.length_cons, List.length_nil]
    omega
  obtain ⟨m, hm⟩ := hlen
  rw [hm]
  unfold fundingBytes fundingScript
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [parseScriptAux_step _ _ _ _ (getOp_numBytes 2 _ hser)]
  rw [parseScriptAux_step _ _ _ _ (getOp_pushBytes pubkey1 _ h1)]
  rw [parseScriptAux_step _ _ _ _ (getOp_pushBytes pubkey2 _ h2)]
  rw [parseScriptAux_step _ _ _ _ (getOp_numBytes 2 _ hser)]
  rw [parseScriptAux_step _ _ _ _ (getOp_op OP_CHECKMULTISIG _ (by decide))]
  rw [parseScriptAux_nil]
  rfl
