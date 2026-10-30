-- Prove2me | solution 1 for BitcoinMiniscript.runSeq_append
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T01:01:08.809035+00:00
-- url     : https://prove2.me/submissions/adc7d570-deb3-43c7-9bb5-db21376708f7

import Definitions.Def_BitcoinMiniscript
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinScript_castToBool_iff

open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

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
    (serialize n).length ≤ k + 1 := by
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

/-- Arithmetic on stack lengths. -/
private theorem toNum_serialize5 (n : Int) (h : n.natAbs < 2 ^ 32) :
    toNum false 5 (serialize n) = some n := by
  unfold toNum
  have := serialize_length n 4 (by simpa using h)
  rw [if_neg (by omega)]
  simp [BitcoinScript.serialize_roundtrip]

private theorem natBytes_zero : natBytes 0 = [] := by rw [natBytes]; rfl

private theorem natBytes_pos (n : Nat) (h : n ≠ 0) :
    natBytes n = BitVec.ofNat 8 (n % 256) :: natBytes (n / 256) := by
  rw [natBytes]; simp [h]

private theorem and_two_pow_eq (n k : Nat) : n &&& 2 ^ k = ((n / 2 ^ k) % 2) * 2 ^ k := by
  have h1 : (n &&& 2 ^ k) / 2 ^ k = (n / 2 ^ k) % 2 := by
    rw [Nat.and_div_two_pow, Nat.div_self (Nat.two_pow_pos k), Nat.and_one_is_mod]
  have h2 : (n &&& 2 ^ k) % 2 ^ k = 0 := by
    rw [Nat.and_mod_two_pow, Nat.mod_self, Nat.and_zero]
  have h := Nat.div_add_mod (n &&& 2 ^ k) (2 ^ k)
  rw [h1, h2, Nat.add_zero, Nat.mul_comm] at h
  exact h.symm

private theorem topbit_false (b : BitcoinScript.Byte) (hb : b.toNat < 128) : ((b &&& 0x80) != 0) = false := by
  have h := and_two_pow_eq b.toNat 7
  have h80 : (0x80 : BitcoinScript.Byte).toNat = 128 := rfl
  have h0 : (0 : BitcoinScript.Byte).toNat = 0 := rfl
  simp only [Nat.reducePow] at h
  rw [bne_eq_false_iff_eq, BitVec.toNat_eq, BitVec.toNat_and, h80, h0, h]
  omega

/-- The top bit of the serialization loop's output is clear below `2^31`. -/
private theorem topBit_natBytes (m : Nat) (hm : m < 2 ^ 31) (ht : topBit (natBytes m) = true) :
    (natBytes m).length ≤ 3 := by
  by_cases h0 : m = 0
  · subst h0; rw [natBytes_zero]; simp
  rw [natBytes_pos m h0]
  by_cases h1 : m / 256 = 0
  · rw [h1, natBytes_zero]; simp
  rw [natBytes_pos _ h1]
  by_cases h2 : m / 256 / 256 = 0
  · rw [h2, natBytes_zero]; simp
  rw [natBytes_pos _ h2]
  by_cases h3 : m / 256 / 256 / 256 = 0
  · rw [h3, natBytes_zero]; simp
  rw [natBytes_pos _ h3]
  have h4 : m / 256 / 256 / 256 / 256 = 0 := by omega
  rw [h4, natBytes_zero]
  exfalso
  rw [natBytes_pos m h0, natBytes_pos _ h1, natBytes_pos _ h2, natBytes_pos _ h3, h4, natBytes_zero] at ht
  simp only [topBit] at ht
  have : (BitVec.ofNat 8 (m / 256 / 256 / 256 % 256)).toNat < 128 := by
    rw [BitVec.toNat_ofNat]; omega
  rw [topbit_false _ this] at ht
  exact Bool.false_ne_true ht

/-- A script number in `0 … 2^31 - 1` serializes to at most 4 bytes. -/
private theorem serialize_len4 (n : Int) (h0 : 0 ≤ n) (h1 : n < 2 ^ 31) : (serialize n).length ≤ 4 := by
  unfold serialize
  split
  · simp
  · dsimp only
    have hm : (natBytes n.natAbs).length ≤ 4 := natBytes_length 4 n.natAbs (by omega)
    split
    · rename_i ht
      have := topBit_natBytes n.natAbs (by omega) ht
      simp only [List.length_append, List.length_singleton]; omega
    · rw [if_neg (by omega)]; exact hm

private theorem toNum4_serialize (n : Int) (h0 : 0 ≤ n) (h1 : n < 2 ^ 31) :
    toNum false nDefaultMaxNumSize (serialize n) = some n := by
  unfold toNum
  have := serialize_len4 n h0 h1
  rw [if_neg (by simp only [nDefaultMaxNumSize]; omega)]
  simp [BitcoinScript.serialize_roundtrip]

private theorem serialize_zero : serialize 0 = [] := by decide +kernel

private theorem serialize_one : serialize 1 = [1] := by decide +kernel

private theorem serialize_32 : serialize 32 = [0x20] := by decide +kernel

private theorem goodVal_nil : GoodVal [] := ⟨0, by decide, by decide, serialize_zero.symm⟩

private theorem goodVal_one : GoodVal [1] := ⟨1, by decide, by decide, serialize_one.symm⟩

private theorem goodVal_bool (b : Bool) : GoodVal (boolBytes b) := by
  cases b
  · exact goodVal_nil
  · exact goodVal_one

private theorem goodVal_toNum (v : Bytes) (h : GoodVal v) :
    toNum false nDefaultMaxNumSize v = some (setVch v) := by
  obtain ⟨n, h0, h1, rfl⟩ := h
  rw [toNum4_serialize n h0 h1, BitcoinScript.serialize_roundtrip]

private theorem setVch_zero_of_false (a : Bytes) (ha : castToBool a = false) : setVch a = 0 := by
  have h := BitcoinScript.castToBool_iff a
  rw [ha] at h
  simpa using h

private theorem setVch_ne_zero_of_true (a : Bytes) (ha : castToBool a = true) : setVch a ≠ 0 :=
  (BitcoinScript.castToBool_iff a).1 ha

/-- `OP_BOOLAND`'s result on two values. -/
private theorem booland_val (a b : Bytes) :
    serialize (if setVch b ≠ 0 ∧ setVch a ≠ 0 then 1 else 0) = boolBytes (castToBool a && castToBool b) := by
  cases ha : castToBool a
  · have hA := setVch_zero_of_false a ha
    rw [if_neg (fun h => h.2 hA)]
    simp [boolBytes, vchFalse, serialize_zero]
  · have hA := setVch_ne_zero_of_true a ha
    cases hb : castToBool b
    · have hB := setVch_zero_of_false b hb
      rw [if_neg (fun h => h.1 hB)]
      simp [boolBytes, vchFalse, serialize_zero]
    · have hB := setVch_ne_zero_of_true b hb
      rw [if_pos ⟨hB, hA⟩]
      simp [boolBytes, vchTrue, serialize_one]

/-- `OP_BOOLOR`'s result on two values. -/
private theorem boolor_val (a b : Bytes) :
    serialize (if setVch b ≠ 0 ∨ setVch a ≠ 0 then 1 else 0) = boolBytes (castToBool a || castToBool b) := by
  cases ha : castToBool a
  · have hA := setVch_zero_of_false a ha
    cases hb : castToBool b
    · have hB := setVch_zero_of_false b hb
      rw [if_neg (fun h => h.elim (fun h' => h' hB) (fun h' => h' hA))]
      simp [boolBytes, vchFalse, serialize_zero]
    · have hB := setVch_ne_zero_of_true b hb
      rw [if_pos (Or.inl hB)]
      simp [boolBytes, vchTrue, serialize_one]
  · have hA := setVch_ne_zero_of_true a ha
    rw [if_pos (Or.inr hA)]
    simp [boolBytes, vchTrue, serialize_one]

/-- `OP_0NOTEQUAL`'s result on a value. -/
private theorem notequal_val (a : Bytes) :
    serialize (if setVch a ≠ 0 then 1 else 0) = boolBytes (castToBool a) := by
  cases ha : castToBool a
  · have hA := setVch_zero_of_false a ha
    rw [if_neg (fun h => h hA)]
    simp [boolBytes, vchFalse, serialize_zero]
  · have hA := setVch_ne_zero_of_true a ha
    rw [if_pos hA]
    simp [boolBytes, vchTrue, serialize_one]

private theorem serialize_length_eq_32 (n : Nat) : (serialize (n : Int) = serialize 32) ↔ n = 32 := by
  constructor
  · intro h
    have h' := congrArg setVch h
    rw [BitcoinScript.serialize_roundtrip, BitcoinScript.serialize_roundtrip] at h'
    omega
  · intro h; subst h; rfl

private theorem castToBool_boolBytes (b : Bool) : castToBool (boolBytes b) = b := by
  cases b <;> rfl

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

private theorem execOp_verify (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_VERIFY s = match s.stack with
      | [] => none
      | top :: rest => if castToBool top then some { s with stack := rest } else none := by
  rfl

private theorem execOp_dup (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_DUP s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := top :: top :: rest } := by
  rfl

private theorem execOp_ifdup (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_IFDUP s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := if castToBool top then top :: top :: rest else top :: rest } := by
  rfl

private theorem execOp_swap (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_SWAP s = match s.stack with
      | a :: b :: rest => some { s with stack := b :: a :: rest }
      | _ => none := by
  rfl

private theorem execOp_toalt (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_TOALTSTACK s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := rest, altstack := top :: s.altstack } := by
  rfl

private theorem execOp_fromalt (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_FROMALTSTACK s = match s.altstack with
      | [] => none
      | top :: rest => some { s with stack := top :: s.stack, altstack := rest } := by
  rfl

private theorem execOp_size (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_SIZE s = match s.stack with
      | [] => none
      | top :: _ => some (pushNum s top.length) := by
  rfl

private theorem execOp_sha256 (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_SHA256 s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := o.sha256 top :: rest } := by
  rfl

private theorem execOp_hash256 (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_HASH256 s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := o.hash256 top :: rest } := by
  rfl

private theorem execOp_ripemd160 (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_RIPEMD160 s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := o.ripemd160 top :: rest } := by
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

private theorem execOp_0notequal (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_0NOTEQUAL s = match s.stack with
      | [] => none
      | top :: rest =>
        match toNum false nDefaultMaxNumSize top with
        | none => none
        | some n => some (pushNum { s with stack := rest } (if n ≠ 0 then 1 else 0)) := by
  rfl

private theorem execOp_booland (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_BOOLAND s = match s.stack with
      | a :: b :: rest =>
        match toNum false nDefaultMaxNumSize b, toNum false nDefaultMaxNumSize a with
        | some n1, some n2 => some (pushNum { s with stack := rest } (if n1 ≠ 0 ∧ n2 ≠ 0 then 1 else 0))
        | _, _ => none
      | _ => none := by
  rfl

private theorem execOp_boolor (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_BOOLOR s = match s.stack with
      | a :: b :: rest =>
        match toNum false nDefaultMaxNumSize b, toNum false nDefaultMaxNumSize a with
        | some n1, some n2 => some (pushNum { s with stack := rest } (if n1 ≠ 0 ∨ n2 ≠ 0 then 1 else 0))
        | _, _ => none
      | _ => none := by
  rfl

private theorem execOp_add (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_ADD s = match s.stack with
      | a :: b :: rest =>
        match toNum false nDefaultMaxNumSize b, toNum false nDefaultMaxNumSize a with
        | some n1, some n2 => some (pushNum { s with stack := rest } (n1 + n2))
        | _, _ => none
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

private theorem csv_step (f : Flags) (o : Oracle) (s : State) (delay : Int) (rest : List Bytes)
    (hs : s.stack = serialize delay :: rest) (hd : delay.natAbs < 2 ^ 32) (hp : CsvPasses f o delay) :
    execOp f o true OP_CHECKSEQUENCEVERIFY s = some s := by
  rw [execOp_csv, hs]
  dsimp only
  rw [toNum_serialize5 delay hd]
  dsimp only
  by_cases hc : f.csv = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false]
    unfold CsvPasses at hp
    simp only [hc, Bool.true_eq_false, false_or] at hp
    obtain ⟨h0, hp⟩ := hp
    rw [if_neg (by omega)]
    rcases hp with hp | hp
    · rw [if_pos (by simpa using hp)]
    · by_cases hdis : (delay.toNat &&& BitcoinScript.SEQUENCE_LOCKTIME_DISABLE_FLAG != 0) = true
      · rw [if_pos hdis]
      · rw [if_neg hdis]; simp [hp]
  · simp only [Bool.not_eq_true] at hc
    simp [hc]

private theorem cltv_step (f : Flags) (o : Oracle) (s : State) (expiry : Int) (rest : List Bytes)
    (hs : s.stack = serialize expiry :: rest) (hd : expiry.natAbs < 2 ^ 32) (hp : CltvPasses f o expiry) :
    execOp f o true OP_CHECKLOCKTIMEVERIFY s = some s := by
  rw [execOp_cltv, hs]
  dsimp only
  rw [toNum_serialize5 expiry hd]
  dsimp only
  by_cases hc : f.cltv = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false]
    unfold CltvPasses at hp
    simp only [hc, Bool.true_eq_false, false_or] at hp
    obtain ⟨h0, hp⟩ := hp
    rw [if_neg (by omega)]
    simp [hp]
  · simp only [Bool.not_eq_true] at hc
    simp [hc]

private theorem step_exec_eq (f : Flags) (o : Oracle) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (c : BitcoinScript.Byte) (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hc : OP_16 < c) (hd : isDisabled c = false) (s' : State)
    (hex : execOp f o true c ⟨st, alt, vf, k + 1⟩ = some s')
    (hsz : s'.stack.length + s'.altstack.length ≤ MAX_STACK_SIZE) :
    step f o ⟨st, alt, vf, k⟩ (.op c) = some s' := by
  rw [step_op_exec f o _ c hc hk hd hvf]
  show (match execOp f o true c ⟨st, alt, vf, k + 1⟩ with
    | none => none
    | some s' => if MAX_STACK_SIZE < s'.stack.length + s'.altstack.length then none else some s') = some s'
  rw [hex]
  dsimp only
  rw [if_neg (by omega)]

private theorem step_cond_eq (f : Flags) (o : Oracle) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (c : BitcoinScript.Byte) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hc : OP_16 < c) (hd : isDisabled c = false) (hcond : OP_IF ≤ c ∧ c ≤ OP_ENDIF) (s' : State)
    (hex : execOp f o (allTrue vf) c ⟨st, alt, vf, k + 1⟩ = some s')
    (hsz : s'.stack.length + s'.altstack.length ≤ MAX_STACK_SIZE) :
    step f o ⟨st, alt, vf, k⟩ (.op c) = some s' := by
  rw [step_op_cond f o _ c hc hk hd hcond]
  show (match execOp f o (allTrue vf) c ⟨st, alt, vf, k + 1⟩ with
    | none => none
    | some s' => if MAX_STACK_SIZE < s'.stack.length + s'.altstack.length then none else some s') = some s'
  rw [hex]
  dsimp only
  rw [if_neg (by omega)]

private theorem sSkip (f : Flags) (o : Oracle) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (c : BitcoinScript.Byte) (hvf : allTrue vf = false) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hc : OP_16 < c) (hd : isDisabled c = false) (hcond : ¬ (OP_IF ≤ c ∧ c ≤ OP_ENDIF))
    (hsz : st.length + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨st, alt, vf, k⟩ (.op c) = some ⟨st, alt, vf, k + 1⟩ := by
  rw [step_op_skip f o _ c hc hk hd hvf hcond]
  dsimp only
  rw [if_neg (by omega)]

private theorem sPush (f : Flags) (o : Oracle) (st alt : List Bytes) (vf : List Bool) (k : Nat) (d : Bytes)
    (hvf : allTrue vf = true) (hd : d.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨st, alt, vf, k⟩ (.push d) = some ⟨d :: st, alt, vf, k⟩ := by
  rw [step_push_exec f o _ d hd hvf]
  dsimp only
  rw [if_neg (by omega)]

private theorem sPushSkip (f : Flags) (o : Oracle) (st alt : List Bytes) (vf : List Bool) (k : Nat) (d : Bytes)
    (hvf : allTrue vf = false) (hd : d.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hsz : st.length + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨st, alt, vf, k⟩ (.push d) = some ⟨st, alt, vf, k⟩ := by
  rw [step_push_skip f o _ d hd hvf]
  dsimp only
  rw [if_neg (by omega)]

private theorem sNum (f : Flags) (o : Oracle) (st alt : List Bytes) (vf : List Bool) (k : Nat) (n : Int)
    (hvf : allTrue vf = true) (hn : (serialize n).length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨st, alt, vf, k⟩ (numInstr n) = some ⟨serialize n :: st, alt, vf, k⟩ := by
  rw [numInstr_exec f o _ n hn hvf]
  dsimp only
  rw [if_neg (by omega)]

private theorem sNumSkip (f : Flags) (o : Oracle) (st alt : List Bytes) (vf : List Bool) (k : Nat) (n : Int)
    (hvf : allTrue vf = false) (hn : (serialize n).length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hsz : st.length + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨st, alt, vf, k⟩ (numInstr n) = some ⟨st, alt, vf, k⟩ := by
  rw [numInstr_skip f o _ n hn hvf]
  dsimp only
  rw [if_neg (by omega)]

private theorem sIf (f : Flags) (o : Oracle) (b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨b :: st, alt, vf, k⟩ (.op OP_IF) = some ⟨st, alt, castToBool b :: vf, k + 1⟩ :=
  step_cond_eq f o _ _ _ _ _ hk (by decide) (by decide) (by decide) _ (by rw [hvf, execOp_if_exec]) (by simp; omega)

private theorem sNotIf (f : Flags) (o : Oracle) (b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨b :: st, alt, vf, k⟩ (.op OP_NOTIF) = some ⟨st, alt, (!castToBool b) :: vf, k + 1⟩ :=
  step_cond_eq f o _ _ _ _ _ hk (by decide) (by decide) (by decide) _ (by rw [hvf, execOp_notif_exec]) (by simp; omega)

private theorem sIfSkip (f : Flags) (o : Oracle) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = false) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨st, alt, vf, k⟩ (.op OP_IF) = some ⟨st, alt, false :: vf, k + 1⟩ :=
  step_cond_eq f o _ _ _ _ _ hk (by decide) (by decide) (by decide) _ (by rw [hvf, execOp_if_skip]) (by simp; omega)

private theorem sNotIfSkip (f : Flags) (o : Oracle) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = false) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨st, alt, vf, k⟩ (.op OP_NOTIF) = some ⟨st, alt, false :: vf, k + 1⟩ :=
  step_cond_eq f o _ _ _ _ _ hk (by decide) (by decide) (by decide) _ (by rw [hvf, execOp_notif_skip]) (by simp; omega)

private theorem sElse (f : Flags) (o : Oracle) (st alt : List Bytes) (b : Bool) (vf : List Bool) (k : Nat)
    (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT) (hsz : st.length + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨st, alt, b :: vf, k⟩ (.op OP_ELSE) = some ⟨st, alt, (!b) :: vf, k + 1⟩ :=
  step_cond_eq f o _ _ _ _ _ hk (by decide) (by decide) (by decide) _ (by rw [execOp_else]) (by simp; omega)

private theorem sEndIf (f : Flags) (o : Oracle) (st alt : List Bytes) (b : Bool) (vf : List Bool) (k : Nat)
    (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT) (hsz : st.length + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨st, alt, b :: vf, k⟩ (.op OP_ENDIF) = some ⟨st, alt, vf, k + 1⟩ :=
  step_cond_eq f o _ _ _ _ _ hk (by decide) (by decide) (by decide) _ (by rw [execOp_endif]) (by simp; omega)

private theorem sVerify (f : Flags) (o : Oracle) (b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + alt.length ≤ MAX_STACK_SIZE) (hb : castToBool b = true) :
    step f o ⟨b :: st, alt, vf, k⟩ (.op OP_VERIFY) = some ⟨st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_verify]; simp [hb]) (by simp; omega)

private theorem sDup (f : Flags) (o : Oracle) (b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 2 + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨b :: st, alt, vf, k⟩ (.op OP_DUP) = some ⟨b :: b :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_dup]) (by simp; omega)

private theorem sIfDupT (f : Flags) (o : Oracle) (b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 2 + alt.length ≤ MAX_STACK_SIZE) (hb : castToBool b = true) :
    step f o ⟨b :: st, alt, vf, k⟩ (.op OP_IFDUP) = some ⟨b :: b :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_ifdup]; simp [hb]) (by simp; omega)

private theorem sIfDupF (f : Flags) (o : Oracle) (b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE) (hb : castToBool b = false) :
    step f o ⟨b :: st, alt, vf, k⟩ (.op OP_IFDUP) = some ⟨b :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_ifdup]; simp [hb]) (by simp; omega)

private theorem sSwap (f : Flags) (o : Oracle) (a b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 2 + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨a :: b :: st, alt, vf, k⟩ (.op OP_SWAP) = some ⟨b :: a :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_swap]) (by simp; omega)

private theorem sToAlt (f : Flags) (o : Oracle) (b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨b :: st, alt, vf, k⟩ (.op OP_TOALTSTACK) = some ⟨st, b :: alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_toalt]) (by simp; omega)

private theorem sFromAlt (f : Flags) (o : Oracle) (b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨st, b :: alt, vf, k⟩ (.op OP_FROMALTSTACK) = some ⟨b :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_fromalt]) (by simp; omega)

private theorem sSize (f : Flags) (o : Oracle) (b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 2 + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨b :: st, alt, vf, k⟩ (.op OP_SIZE) = some ⟨serialize b.length :: b :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_size]; rfl) (by simp; omega)

private theorem sSha256 (f : Flags) (o : Oracle) (b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨b :: st, alt, vf, k⟩ (.op OP_SHA256) = some ⟨o.sha256 b :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_sha256]) (by simp; omega)

private theorem sHash256 (f : Flags) (o : Oracle) (b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨b :: st, alt, vf, k⟩ (.op OP_HASH256) = some ⟨o.hash256 b :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_hash256]) (by simp; omega)

private theorem sRipemd160 (f : Flags) (o : Oracle) (b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨b :: st, alt, vf, k⟩ (.op OP_RIPEMD160) = some ⟨o.ripemd160 b :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_ripemd160]) (by simp; omega)

private theorem sHash160 (f : Flags) (o : Oracle) (b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨b :: st, alt, vf, k⟩ (.op OP_HASH160) = some ⟨o.hash160 b :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_hash160]) (by simp; omega)

private theorem sEqual (f : Flags) (o : Oracle) (a b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE) :
    step f o ⟨a :: b :: st, alt, vf, k⟩ (.op OP_EQUAL) = some ⟨boolBytes (decide (b = a)) :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_equal]) (by simp; omega)

private theorem sEqualVerify (f : Flags) (o : Oracle) (a b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + alt.length ≤ MAX_STACK_SIZE) (heq : b = a) :
    step f o ⟨a :: b :: st, alt, vf, k⟩ (.op OP_EQUALVERIFY) = some ⟨st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_equalverify]; simp [heq]) (by simp; omega)

private theorem sCheckSig (f : Flags) (o : Oracle) (pk sig : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (ok : Bool) (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE) (hcs : o.checkSig sig pk = some ok) :
    step f o ⟨pk :: sig :: st, alt, vf, k⟩ (.op OP_CHECKSIG) = some ⟨boolBytes ok :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_checksig]; simp [hcs]) (by simp; omega)

private theorem s0NotEqual (f : Flags) (o : Oracle) (a : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (n : Int) (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE) (ha : toNum false nDefaultMaxNumSize a = some n) :
    step f o ⟨a :: st, alt, vf, k⟩ (.op OP_0NOTEQUAL) =
      some ⟨serialize (if n ≠ 0 then 1 else 0) :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_0notequal]; simp [ha]; rfl) (by simp; omega)

private theorem sBoolAnd (f : Flags) (o : Oracle) (a b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (n1 n2 : Int) (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE)
    (ha : toNum false nDefaultMaxNumSize a = some n2) (hb : toNum false nDefaultMaxNumSize b = some n1) :
    step f o ⟨a :: b :: st, alt, vf, k⟩ (.op OP_BOOLAND) =
      some ⟨serialize (if n1 ≠ 0 ∧ n2 ≠ 0 then 1 else 0) :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_booland]; simp [ha, hb]; rfl) (by simp; omega)

private theorem sBoolOr (f : Flags) (o : Oracle) (a b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (n1 n2 : Int) (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE)
    (ha : toNum false nDefaultMaxNumSize a = some n2) (hb : toNum false nDefaultMaxNumSize b = some n1) :
    step f o ⟨a :: b :: st, alt, vf, k⟩ (.op OP_BOOLOR) =
      some ⟨serialize (if n1 ≠ 0 ∨ n2 ≠ 0 then 1 else 0) :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_boolor]; simp [ha, hb]; rfl) (by simp; omega)

private theorem sAdd (f : Flags) (o : Oracle) (a b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (n1 n2 : Int) (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE)
    (ha : toNum false nDefaultMaxNumSize a = some n2) (hb : toNum false nDefaultMaxNumSize b = some n1) :
    step f o ⟨a :: b :: st, alt, vf, k⟩ (.op OP_ADD) = some ⟨serialize (n1 + n2) :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (by rw [execOp_add]; simp [ha, hb]; rfl) (by simp; omega)

private theorem sCsv (f : Flags) (o : Oracle) (n : Int) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE) (hn : n.natAbs < 2 ^ 32) (hp : CsvPasses f o n) :
    step f o ⟨serialize n :: st, alt, vf, k⟩ (.op OP_CHECKSEQUENCEVERIFY) = some ⟨serialize n :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (csv_step f o _ n st rfl hn hp) (by simp; omega)

private theorem sCltv (f : Flags) (o : Oracle) (n : Int) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = true) (hk : k + 1 ≤ MAX_OPS_PER_SCRIPT)
    (hsz : st.length + 1 + alt.length ≤ MAX_STACK_SIZE) (hn : n.natAbs < 2 ^ 32) (hp : CltvPasses f o n) :
    step f o ⟨serialize n :: st, alt, vf, k⟩ (.op OP_CHECKLOCKTIMEVERIFY) = some ⟨serialize n :: st, alt, vf, k + 1⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf hk (by decide) (by decide) _ (cltv_step f o _ n st rfl hn hp) (by simp; omega)

/-- `runSeq` composes sequentially. -/
theorem solution (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle)
    (s : BitcoinScript.State) (a b : BitcoinScript.Script) :
    BitcoinMiniscript.runSeq f o s (a ++ b) =
      match BitcoinMiniscript.runSeq f o s a with
      | none => none
      | some s' => BitcoinMiniscript.runSeq f o s' b := by
  induction a generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.cons_append, runSeq]
    cases step f o s i with
    | none => rfl
    | some s' => exact ih s'
