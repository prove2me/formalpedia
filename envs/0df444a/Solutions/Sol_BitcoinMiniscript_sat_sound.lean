-- Prove2me | solution 1 for BitcoinMiniscript.sat_sound
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T01:04:15.260913+00:00
-- url     : https://prove2.me/submissions/a9f9799f-d679-4c53-8d34-bb28a6486a11

import Definitions.Def_BitcoinMiniscript
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinScript_castToBool_iff
import Theorems.Thm_BitcoinMiniscript_runSeq_append
import Theorems.Thm_BitcoinMiniscript_sem_sound

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

private def Runs (f : Flags) (o : Oracle) (sc : Script) (s s' : State) : Prop := runSeq f o s sc = some s'

private theorem runs_nil (f : Flags) (o : Oracle) (s : State) : Runs f o [] s s := rfl

private theorem runs_one {f : Flags} {o : Oracle} {i : Instr} {s s' : State} (h : step f o s i = some s') :
    Runs f o [i] s s' := by
  unfold Runs; simp only [runSeq, h]

private theorem runs_app {f : Flags} {o : Oracle} {a b : Script} {s s1 s2 : State}
    (h1 : Runs f o a s s1) (h2 : Runs f o b s1 s2) : Runs f o (a ++ b) s s2 := by
  unfold Runs at *
  rw [BitcoinMiniscript.runSeq_append, h1]
  exact h2

private theorem runs_assoc {f : Flags} {o : Oracle} {sc : Script} {a b c alt : List Bytes} {vf : List Bool} {k : Nat}
    {s' : State} (h : Runs f o sc ⟨a ++ (b ++ c), alt, vf, k⟩ s') : Runs f o sc ⟨(a ++ b) ++ c, alt, vf, k⟩ s' := by
  rw [List.append_assoc]; exact h

private theorem allTrue_cons (b : Bool) (l : List Bool) : allTrue (b :: l) = (b && allTrue l) := by
  simp [allTrue, List.all_cons]

private theorem sem_zo (f : Flags) (o : Oracle) (m : Ms) : ∀ (w out : List Bytes), Sem f o m w out →
    ((props m).z = true → w = []) ∧ ((props m).o = true → w.length = 1) := by
  induction m with
  | pk_k key => intro w out h; obtain ⟨sig, rfl, -⟩ := h; simp [props]
  | pk_h hh => intro w out h; obtain ⟨key, sig, rfl, -, -⟩ := h; simp [props]
  | older n => intro w out h; obtain ⟨rfl, -, -⟩ := h; simp [props]
  | after n => intro w out h; obtain ⟨rfl, -, -⟩ := h; simp [props]
  | sha256 hh => intro w out h; obtain ⟨pre, rfl, -, -⟩ := h; simp [props]
  | hash256 hh => intro w out h; obtain ⟨pre, rfl, -, -⟩ := h; simp [props]
  | ripemd160 hh => intro w out h; obtain ⟨pre, rfl, -, -⟩ := h; simp [props]
  | hash160 hh => intro w out h; obtain ⟨pre, rfl, -, -⟩ := h; simp [props]
  | and_v x y ihx ihy =>
    intro w out h
    obtain ⟨wx, wy, rfl, hx, hy⟩ := h
    obtain ⟨zx, ox⟩ := ihx _ _ hx
    obtain ⟨zy, oy⟩ := ihy _ _ hy
    simp only [props, Bool.and_eq_true, Bool.or_eq_true, List.length_append]
    constructor
    · intro ⟨h1, h2⟩; rw [zx h1, zy h2]; rfl
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [zx h1, oy h2]; rfl
      · rw [ox h1, zy h2]; rfl
  | and_b x y ihx ihy =>
    intro w out h
    obtain ⟨wx, wy, vx, vy, rfl, hx, hy, -⟩ := h
    obtain ⟨zx, ox⟩ := ihx _ _ hx
    obtain ⟨zy, oy⟩ := ihy _ _ hy
    simp only [props, Bool.and_eq_true, Bool.or_eq_true, List.length_append]
    constructor
    · intro ⟨h1, h2⟩; rw [zx h1, zy h2]; rfl
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [zx h1, oy h2]; rfl
      · rw [ox h1, zy h2]; rfl
  | or_b x z ihx ihz =>
    intro w out h
    obtain ⟨wx, wz, vx, vz, rfl, hx, hz, -⟩ := h
    obtain ⟨zx, ox⟩ := ihx _ _ hx
    obtain ⟨zz, oz⟩ := ihz _ _ hz
    simp only [props, Bool.and_eq_true, Bool.or_eq_true, List.length_append]
    constructor
    · intro ⟨h1, h2⟩; rw [zx h1, zz h2]; rfl
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [zx h1, oz h2]; rfl
      · rw [ox h1, zz h2]; rfl
  | or_c x z ihx ihz =>
    intro w out h
    obtain ⟨-, wx, vx, hx, h⟩ := h
    obtain ⟨zx, ox⟩ := ihx _ _ hx
    simp only [props, Bool.and_eq_true]
    rcases h with ⟨-, rfl⟩ | ⟨-, wz, rfl, hz⟩
    · exact ⟨fun h => zx h.1, fun h => ox h.1⟩
    · obtain ⟨zz, oz⟩ := ihz _ _ hz
      simp only [List.length_append]
      constructor
      · intro ⟨h1, h2⟩; rw [zx h1, zz h2]; rfl
      · intro ⟨h1, h2⟩; rw [ox h1, zz h2]; rfl
  | or_d x z ihx ihz =>
    intro w out h
    obtain ⟨wx, vx, hx, h⟩ := h
    obtain ⟨zx, ox⟩ := ihx _ _ hx
    simp only [props, Bool.and_eq_true]
    rcases h with ⟨-, rfl, -⟩ | ⟨-, wz, rfl, hz⟩
    · exact ⟨fun h => zx h.1, fun h => ox h.1⟩
    · obtain ⟨zz, oz⟩ := ihz _ _ hz
      simp only [List.length_append]
      constructor
      · intro ⟨h1, h2⟩; rw [zx h1, zz h2]; rfl
      · intro ⟨h1, h2⟩; rw [ox h1, zz h2]; rfl
  | or_i x z ihx ihz =>
    intro w out h
    obtain ⟨b, w', rfl, h⟩ := h
    simp only [props, Bool.and_eq_true, Bool.false_eq_true, false_imp_iff, true_and, List.length_cons]
    rcases h with ⟨-, hx⟩ | ⟨-, hz⟩
    · intro ⟨h1, _⟩; rw [(ihx _ _ hx).1 h1]; rfl
    · intro ⟨_, h2⟩; rw [(ihz _ _ hz).1 h2]; rfl
  | andor x y z ihx ihy ihz =>
    intro w out h
    obtain ⟨wx, vx, hx, h⟩ := h
    obtain ⟨zx, ox⟩ := ihx _ _ hx
    simp only [props, Bool.and_eq_true, Bool.or_eq_true]
    rcases h with ⟨-, wy, rfl, hy⟩ | ⟨-, wz, rfl, hz⟩
    · obtain ⟨zy, oy⟩ := ihy _ _ hy
      simp only [List.length_append]
      constructor
      · intro ⟨⟨h1, h2⟩, _⟩; rw [zx h1, zy h2]; rfl
      · intro h
        rcases h with ⟨⟨h1, h2⟩, _⟩ | ⟨⟨h1, h2⟩, _⟩
        · rw [zx h1, oy h2]; rfl
        · rw [ox h1, zy h2]; rfl
    · obtain ⟨zz, oz⟩ := ihz _ _ hz
      simp only [List.length_append]
      constructor
      · intro ⟨⟨h1, _⟩, h3⟩; rw [zx h1, zz h3]; rfl
      · intro h
        rcases h with ⟨⟨h1, _⟩, h3⟩ | ⟨⟨h1, _⟩, h3⟩
        · rw [zx h1, oz h3]; rfl
        · rw [ox h1, zz h3]; rfl
  | multi k keys => intro w out h; simp [props]
  | wrap_a x ihx => intro w out h; simp [props]
  | wrap_s x ihx =>
    intro w out h
    simp only [props, Bool.false_eq_true, false_imp_iff, true_and]
    exact (ihx _ _ h).2
  | wrap_c x ihx =>
    intro w out h
    obtain ⟨key, sig, ok, hx, -, -⟩ := h
    simp only [props, Bool.false_eq_true, false_imp_iff, true_and]
    exact (ihx _ _ hx).2
  | wrap_d x ihx =>
    intro w out h
    simp only [props, Bool.false_eq_true, false_imp_iff, true_and]
    rcases h with ⟨rfl, -, -⟩ | ⟨rfl, -⟩ <;> intro _ <;> rfl
  | wrap_v x ihx =>
    intro w out h
    obtain ⟨v, hx, -, -⟩ := h
    simp only [props]
    exact ihx _ _ hx
  | wrap_j x ihx =>
    intro w out h
    simp only [props, Bool.false_eq_true, false_imp_iff, true_and]
    rcases h with ⟨e, w', rfl, -, -, hx⟩ | ⟨rfl, -⟩
    · exact (ihx _ _ hx).2
    · intro _; rfl
  | wrap_n x ihx =>
    intro w out h
    obtain ⟨v, hx, -⟩ := h
    simp only [props]
    exact ihx _ _ hx

private def SkipSpec (f : Flags) (o : Oracle) (m : Ms) : Prop :=
  ∀ (st alt : List Bytes) (vf : List Bool) (k : Nat), allTrue vf = false →
    k + opsMax m ≤ MAX_OPS_PER_SCRIPT → st.length + alt.length ≤ MAX_STACK_SIZE →
    ∃ k', Runs f o (compile m) ⟨st, alt, vf, k⟩ ⟨st, alt, vf, k'⟩ ∧ k' ≤ k + opsMax m

private theorem ser_len_small (n : Int) (h0 : 0 ≤ n) (h1 : n < 2 ^ 31) :
    (serialize n).length ≤ MAX_SCRIPT_ELEMENT_SIZE :=
  Nat.le_trans (serialize_len4 n h0 h1) (by decide)

private theorem ser32_len : (serialize 32).length ≤ MAX_SCRIPT_ELEMENT_SIZE := by
  rw [serialize_32]; decide

private theorem runs_pushes_skip (f : Flags) (o : Oracle) (keys : List Bytes)
    (hkeys : ∀ key ∈ keys, key.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (st alt : List Bytes) (vf : List Bool) (k : Nat)
    (hvf : allTrue vf = false) (hsz : st.length + alt.length ≤ MAX_STACK_SIZE) :
    Runs f o (keys.map Instr.push) ⟨st, alt, vf, k⟩ ⟨st, alt, vf, k⟩ := by
  induction keys with
  | nil => exact runs_nil f o _
  | cons key rest ih =>
    simp only [List.map_cons]
    have h1 := sPushSkip f o st alt vf k key hvf (hkeys key (List.mem_cons_self ..)) hsz
    have h2 := ih (fun key' hk => hkeys key' (List.mem_cons_of_mem _ hk))
    unfold Runs at h2 ⊢
    simp only [runSeq, h1]
    exact h2

private theorem skip_of_hasType (f : Flags) (o : Oracle) {m : Ms} {ty : Ty} (ht : HasType m ty) :
    SkipSpec f o m := by
  induction ht with
  | pk_k key hkey =>
    intro st alt vf k hvf hk hsz
    exact ⟨k, runs_one (sPushSkip f o st alt vf k key hvf hkey hsz), by simp [opsMax]⟩
  | pk_h hh hlen =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    refine ⟨k + 3, ?_, by simp [opsMax]⟩
    exact runs_app (runs_app (runs_app
      (runs_one (sSkip f o st alt vf k OP_DUP hvf (by omega) (by decide) (by decide) (by decide) hsz))
      (runs_one (sSkip f o st alt vf (k + 1) OP_HASH160 hvf (by omega) (by decide) (by decide) (by decide) hsz)))
      (runs_one (sPushSkip f o st alt vf (k + 2) hh hvf hlen hsz)))
      (runs_one (sSkip f o st alt vf (k + 2) OP_EQUALVERIFY hvf (by omega) (by decide) (by decide) (by decide) hsz))
  | older n h1 h2 =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    refine ⟨k + 1, ?_, by simp [opsMax]⟩
    exact runs_app (runs_one (sNumSkip f o st alt vf k n hvf (ser_len_small n (by omega) h2) hsz))
      (runs_one (sSkip f o st alt vf k OP_CHECKSEQUENCEVERIFY hvf (by omega) (by decide) (by decide) (by decide) hsz))
  | after n h1 h2 =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    refine ⟨k + 1, ?_, by simp [opsMax]⟩
    exact runs_app (runs_one (sNumSkip f o st alt vf k n hvf (ser_len_small n (by omega) h2) hsz))
      (runs_one (sSkip f o st alt vf k OP_CHECKLOCKTIMEVERIFY hvf (by omega) (by decide) (by decide) (by decide) hsz))
  | sha256 hh hlen =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    refine ⟨k + 4, ?_, by simp [opsMax]⟩
    exact runs_app (runs_app (runs_app (runs_app (runs_app
      (runs_one (sSkip f o st alt vf k OP_SIZE hvf (by omega) (by decide) (by decide) (by decide) hsz))
      (runs_one (sNumSkip f o st alt vf (k + 1) 32 hvf ser32_len hsz)))
      (runs_one (sSkip f o st alt vf (k + 1) OP_EQUALVERIFY hvf (by omega) (by decide) (by decide) (by decide) hsz)))
      (runs_one (sSkip f o st alt vf (k + 2) OP_SHA256 hvf (by omega) (by decide) (by decide) (by decide) hsz)))
      (runs_one (sPushSkip f o st alt vf (k + 3) hh hvf hlen hsz)))
      (runs_one (sSkip f o st alt vf (k + 3) OP_EQUAL hvf (by omega) (by decide) (by decide) (by decide) hsz))
  | hash256 hh hlen =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    refine ⟨k + 4, ?_, by simp [opsMax]⟩
    exact runs_app (runs_app (runs_app (runs_app (runs_app
      (runs_one (sSkip f o st alt vf k OP_SIZE hvf (by omega) (by decide) (by decide) (by decide) hsz))
      (runs_one (sNumSkip f o st alt vf (k + 1) 32 hvf ser32_len hsz)))
      (runs_one (sSkip f o st alt vf (k + 1) OP_EQUALVERIFY hvf (by omega) (by decide) (by decide) (by decide) hsz)))
      (runs_one (sSkip f o st alt vf (k + 2) OP_HASH256 hvf (by omega) (by decide) (by decide) (by decide) hsz)))
      (runs_one (sPushSkip f o st alt vf (k + 3) hh hvf hlen hsz)))
      (runs_one (sSkip f o st alt vf (k + 3) OP_EQUAL hvf (by omega) (by decide) (by decide) (by decide) hsz))
  | ripemd160 hh hlen =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    refine ⟨k + 4, ?_, by simp [opsMax]⟩
    exact runs_app (runs_app (runs_app (runs_app (runs_app
      (runs_one (sSkip f o st alt vf k OP_SIZE hvf (by omega) (by decide) (by decide) (by decide) hsz))
      (runs_one (sNumSkip f o st alt vf (k + 1) 32 hvf ser32_len hsz)))
      (runs_one (sSkip f o st alt vf (k + 1) OP_EQUALVERIFY hvf (by omega) (by decide) (by decide) (by decide) hsz)))
      (runs_one (sSkip f o st alt vf (k + 2) OP_RIPEMD160 hvf (by omega) (by decide) (by decide) (by decide) hsz)))
      (runs_one (sPushSkip f o st alt vf (k + 3) hh hvf hlen hsz)))
      (runs_one (sSkip f o st alt vf (k + 3) OP_EQUAL hvf (by omega) (by decide) (by decide) (by decide) hsz))
  | hash160 hh hlen =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    refine ⟨k + 4, ?_, by simp [opsMax]⟩
    exact runs_app (runs_app (runs_app (runs_app (runs_app
      (runs_one (sSkip f o st alt vf k OP_SIZE hvf (by omega) (by decide) (by decide) (by decide) hsz))
      (runs_one (sNumSkip f o st alt vf (k + 1) 32 hvf ser32_len hsz)))
      (runs_one (sSkip f o st alt vf (k + 1) OP_EQUALVERIFY hvf (by omega) (by decide) (by decide) (by decide) hsz)))
      (runs_one (sSkip f o st alt vf (k + 2) OP_HASH160 hvf (by omega) (by decide) (by decide) (by decide) hsz)))
      (runs_one (sPushSkip f o st alt vf (k + 3) hh hvf hlen hsz)))
      (runs_one (sSkip f o st alt vf (k + 3) OP_EQUAL hvf (by omega) (by decide) (by decide) (by decide) hsz))
  | and_v hx hy hne ihx ihy =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    obtain ⟨k1, h1, hk1⟩ := ihx st alt vf k hvf (by omega) hsz
    obtain ⟨k2, h2, hk2⟩ := ihy st alt vf k1 hvf (by omega) hsz
    exact ⟨k2, runs_app h1 h2, by simp only [opsMax]; omega⟩
  | and_b hx hy ihx ihy =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    obtain ⟨k1, h1, hk1⟩ := ihx st alt vf k hvf (by omega) hsz
    obtain ⟨k2, h2, hk2⟩ := ihy st alt vf k1 hvf (by omega) hsz
    exact ⟨k2 + 1, runs_app (runs_app h1 h2)
      (runs_one (sSkip f o st alt vf k2 OP_BOOLAND hvf (by omega) (by decide) (by decide) (by decide) hsz)),
      by simp only [opsMax]; omega⟩
  | or_b hx hdx hz hdz ihx ihz =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    obtain ⟨k1, h1, hk1⟩ := ihx st alt vf k hvf (by omega) hsz
    obtain ⟨k2, h2, hk2⟩ := ihz st alt vf k1 hvf (by omega) hsz
    exact ⟨k2 + 1, runs_app (runs_app h1 h2)
      (runs_one (sSkip f o st alt vf k2 OP_BOOLOR hvf (by omega) (by decide) (by decide) (by decide) hsz)),
      by simp only [opsMax]; omega⟩
  | or_c hx hdx hux hz ihx ihz =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    obtain ⟨k1, h1, hk1⟩ := ihx st alt vf k hvf (by omega) hsz
    have hvf' : allTrue (false :: vf) = false := by rw [allTrue_cons]; simp
    obtain ⟨k2, h2, hk2⟩ := ihz st alt (false :: vf) (k1 + 1) hvf' (by omega) hsz
    exact ⟨k2 + 1, runs_app (runs_app (runs_app h1
      (runs_one (sNotIfSkip f o st alt vf k1 hvf (by omega) hsz))) h2)
      (runs_one (sEndIf f o st alt false vf k2 (by omega) hsz)),
      by simp only [opsMax]; omega⟩
  | or_d hx hdx hux hz ihx ihz =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    obtain ⟨k1, h1, hk1⟩ := ihx st alt vf k hvf (by omega) hsz
    have hvf' : allTrue (false :: vf) = false := by rw [allTrue_cons]; simp
    obtain ⟨k2, h2, hk2⟩ := ihz st alt (false :: vf) (k1 + 2) hvf' (by omega) hsz
    exact ⟨k2 + 1, runs_app (runs_app (runs_app (runs_app h1
      (runs_one (sSkip f o st alt vf k1 OP_IFDUP hvf (by omega) (by decide) (by decide) (by decide) hsz)))
      (runs_one (sNotIfSkip f o st alt vf (k1 + 1) hvf (by omega) hsz))) h2)
      (runs_one (sEndIf f o st alt false vf k2 (by omega) hsz)),
      by simp only [opsMax]; omega⟩
  | or_i hx hz hne ihx ihz =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    have hvf' : allTrue (false :: vf) = false := by rw [allTrue_cons]; simp
    have hvf'' : allTrue (true :: vf) = false := by rw [allTrue_cons]; simp [hvf]
    obtain ⟨k1, h1, hk1⟩ := ihx st alt (false :: vf) (k + 1) hvf' (by omega) hsz
    obtain ⟨k2, h2, hk2⟩ := ihz st alt ((!false) :: vf) (k1 + 1) (by simpa using hvf'') (by omega) hsz
    exact ⟨k2 + 1, runs_app (runs_app (runs_app (runs_app
      (runs_one (sIfSkip f o st alt vf k hvf (by omega) hsz)) h1)
      (runs_one (sElse f o st alt false vf k1 (by omega) hsz))) h2)
      (runs_one (sEndIf f o st alt _ vf k2 (by omega) hsz)),
      by simp only [opsMax]; omega⟩
  | andor hx hdx hux hy hz hne ihx ihy ihz =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    have hvf' : allTrue (false :: vf) = false := by rw [allTrue_cons]; simp
    have hvf'' : allTrue (true :: vf) = false := by rw [allTrue_cons]; simp [hvf]
    obtain ⟨k1, h1, hk1⟩ := ihx st alt vf k hvf (by omega) hsz
    obtain ⟨k2, h2, hk2⟩ := ihz st alt (false :: vf) (k1 + 1) hvf' (by omega) hsz
    obtain ⟨k3, h3, hk3⟩ := ihy st alt ((!false) :: vf) (k2 + 1) (by simpa using hvf'') (by omega) hsz
    exact ⟨k3 + 1, runs_app (runs_app (runs_app (runs_app (runs_app h1
      (runs_one (sNotIfSkip f o st alt vf k1 hvf (by omega) hsz))) h2)
      (runs_one (sElse f o st alt false vf k2 (by omega) hsz))) h3)
      (runs_one (sEndIf f o st alt _ vf k3 (by omega) hsz)),
      by simp only [opsMax]; omega⟩
  | multi kk keys hk1 hk2 hk3 hkeys =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    refine ⟨k + 1, ?_, by simp [opsMax]⟩
    have hkk : (serialize (kk : Int)).length ≤ MAX_SCRIPT_ELEMENT_SIZE :=
      ser_len_small _ (by omega) (by simp only [MAX_PUBKEYS_PER_MULTISIG] at hk3; omega)
    have hnn : (serialize (keys.length : Int)).length ≤ MAX_SCRIPT_ELEMENT_SIZE :=
      ser_len_small _ (by omega) (by simp only [MAX_PUBKEYS_PER_MULTISIG] at hk3; omega)
    exact runs_app (runs_app (runs_app
      (runs_one (sNumSkip f o st alt vf k kk hvf hkk hsz))
      (runs_pushes_skip f o keys hkeys st alt vf k hvf hsz))
      (runs_one (sNumSkip f o st alt vf k keys.length hvf hnn hsz)))
      (runs_one (sSkip f o st alt vf k OP_CHECKMULTISIG hvf (by omega) (by decide) (by decide) (by decide) hsz))
  | wrap_a hx ihx =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    obtain ⟨k1, h1, hk1⟩ := ihx st alt vf (k + 1) hvf (by omega) hsz
    exact ⟨k1 + 1, runs_app (runs_app
      (runs_one (sSkip f o st alt vf k OP_TOALTSTACK hvf (by omega) (by decide) (by decide) (by decide) hsz)) h1)
      (runs_one (sSkip f o st alt vf k1 OP_FROMALTSTACK hvf (by omega) (by decide) (by decide) (by decide) hsz)),
      by simp only [opsMax]; omega⟩
  | wrap_s hx hox ihx =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    obtain ⟨k1, h1, hk1⟩ := ihx st alt vf (k + 1) hvf (by omega) hsz
    exact ⟨k1, runs_app
      (runs_one (sSkip f o st alt vf k OP_SWAP hvf (by omega) (by decide) (by decide) (by decide) hsz)) h1,
      by simp only [opsMax]; omega⟩
  | wrap_c hx ihx =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    obtain ⟨k1, h1, hk1⟩ := ihx st alt vf k hvf (by omega) hsz
    exact ⟨k1 + 1, runs_app h1
      (runs_one (sSkip f o st alt vf k1 OP_CHECKSIG hvf (by omega) (by decide) (by decide) (by decide) hsz)),
      by simp only [opsMax]; omega⟩
  | wrap_d hx hzx ihx =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    have hvf' : allTrue (false :: vf) = false := by rw [allTrue_cons]; simp
    obtain ⟨k1, h1, hk1⟩ := ihx st alt (false :: vf) (k + 2) hvf' (by omega) hsz
    exact ⟨k1 + 1, runs_app (runs_app (runs_app
      (runs_one (sSkip f o st alt vf k OP_DUP hvf (by omega) (by decide) (by decide) (by decide) hsz))
      (runs_one (sIfSkip f o st alt vf (k + 1) hvf (by omega) hsz))) h1)
      (runs_one (sEndIf f o st alt false vf k1 (by omega) hsz)),
      by simp only [opsMax]; omega⟩
  | wrap_v hx ihx =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    obtain ⟨k1, h1, hk1⟩ := ihx st alt vf k hvf (by omega) hsz
    exact ⟨k1 + 1, runs_app h1
      (runs_one (sSkip f o st alt vf k1 OP_VERIFY hvf (by omega) (by decide) (by decide) (by decide) hsz)),
      by simp only [opsMax]; omega⟩
  | wrap_j hx hnx ihx =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    have hvf' : allTrue (false :: vf) = false := by rw [allTrue_cons]; simp
    obtain ⟨k1, h1, hk1⟩ := ihx st alt (false :: vf) (k + 3) hvf' (by omega) hsz
    exact ⟨k1 + 1, runs_app (runs_app (runs_app (runs_app
      (runs_one (sSkip f o st alt vf k OP_SIZE hvf (by omega) (by decide) (by decide) (by decide) hsz))
      (runs_one (sSkip f o st alt vf (k + 1) OP_0NOTEQUAL hvf (by omega) (by decide) (by decide) (by decide) hsz)))
      (runs_one (sIfSkip f o st alt vf (k + 2) hvf (by omega) hsz))) h1)
      (runs_one (sEndIf f o st alt false vf k1 (by omega) hsz)),
      by simp only [opsMax]; omega⟩
  | wrap_n hx ihx =>
    intro st alt vf k hvf hk hsz
    simp only [opsMax] at hk
    obtain ⟨k1, h1, hk1⟩ := ihx st alt vf k hvf (by omega) hsz
    exact ⟨k1 + 1, runs_app h1
      (runs_one (sSkip f o st alt vf k1 OP_0NOTEQUAL hvf (by omega) (by decide) (by decide) (by decide) hsz)),
      by simp only [opsMax]; omega⟩

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

private theorem cms_exec (f : Flags) (o : Oracle) (keys sigs : List Bytes) (dummy : Bytes) (rest alt : List Bytes)
    (vf : List Bool) (k : Nat) (ok : Bool)
    (hn : keys.length ≤ MAX_PUBKEYS_PER_MULTISIG) (hk : sigs.length ≤ keys.length)
    (hops : k + keys.length ≤ MAX_OPS_PER_SCRIPT)
    (hloop : multisigLoop o sigs keys.reverse = some ok) (hdummy : f.nulldummy = true → dummy = []) :
    execOp f o true OP_CHECKMULTISIG
        ⟨serialize keys.length :: (keys.reverse ++ serialize sigs.length :: (sigs ++ dummy :: rest)), alt, vf, k⟩ =
      some ⟨boolBytes ok :: rest, alt, vf, k + keys.length⟩ := by
  rw [execOp_cms]
  dsimp only
  simp only [MAX_PUBKEYS_PER_MULTISIG] at hn
  rw [toNum4_serialize _ (by omega) (by omega)]
  dsimp only
  rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]; simp only [MAX_PUBKEYS_PER_MULTISIG]; omega)]
  rw [if_neg (by simp only [Int.toNat_natCast]; omega)]
  simp only [Int.toNat_natCast]
  rw [List.take_left' (by simp), List.drop_left' (by simp)]
  simp only [List.length_reverse, ne_eq, not_true_eq_false, ite_false]
  rw [toNum4_serialize _ (by omega) (by omega)]
  dsimp only
  rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]; omega)]
  simp only [Int.toNat_natCast]
  rw [List.take_left' rfl, List.drop_left' rfl]
  simp only [ne_eq, not_true_eq_false, ite_false, hloop]
  rw [if_neg]
  cases hnd : f.nulldummy
  · simp
  · simp [hdummy hnd]

private theorem sCms (f : Flags) (o : Oracle) (keys sigs : List Bytes) (dummy : Bytes) (rest alt : List Bytes)
    (vf : List Bool) (k : Nat) (ok : Bool) (hvf : allTrue vf = true)
    (hn : keys.length ≤ MAX_PUBKEYS_PER_MULTISIG) (hk : sigs.length ≤ keys.length)
    (hops : k + 1 + keys.length ≤ MAX_OPS_PER_SCRIPT) (hsz : rest.length + 1 + alt.length ≤ MAX_STACK_SIZE)
    (hloop : multisigLoop o sigs keys.reverse = some ok) (hdummy : f.nulldummy = true → dummy = []) :
    step f o ⟨serialize keys.length :: (keys.reverse ++ serialize sigs.length :: (sigs ++ dummy :: rest)), alt, vf, k⟩
        (.op OP_CHECKMULTISIG) =
      some ⟨boolBytes ok :: rest, alt, vf, k + 1 + keys.length⟩ :=
  step_exec_eq f o _ _ _ _ _ hvf (by omega) (by decide) (by decide) _
    (cms_exec f o keys sigs dummy rest alt vf (k + 1) ok hn hk (by omega) hloop hdummy) (by simp; omega)

private theorem runs_pushes (f : Flags) (o : Oracle) (keys : List Bytes)
    (hkeys : ∀ key ∈ keys, key.length ≤ MAX_SCRIPT_ELEMENT_SIZE) : ∀ (st alt : List Bytes) (vf : List Bool) (k : Nat),
    allTrue vf = true → st.length + keys.length + alt.length ≤ MAX_STACK_SIZE →
    Runs f o (keys.map Instr.push) ⟨st, alt, vf, k⟩ ⟨keys.reverse ++ st, alt, vf, k⟩ := by
  induction keys with
  | nil => intro st alt vf k _ _; exact runs_nil f o _
  | cons key rest ih =>
    intro st alt vf k hvf hsz
    simp only [List.length_cons] at hsz
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    have h1 := sPush f o st alt vf k key hvf (hkeys key (List.mem_cons_self ..)) (by omega)
    have h2 := ih (fun key' hk => hkeys key' (List.mem_cons_of_mem _ hk)) (key :: st) alt vf k hvf
      (by simp only [List.length_cons]; omega)
    unfold Runs at h2 ⊢
    simp only [runSeq, h1]
    exact h2

private def RunSpec (f : Flags) (o : Oracle) (sc : Script) (inp out : List Bytes) (ops sz : Nat) : Prop :=
  ∀ (rest alt : List Bytes) (vf : List Bool) (k : Nat), allTrue vf = true → k + ops ≤ MAX_OPS_PER_SCRIPT →
    inp.length + rest.length + alt.length + sz ≤ MAX_STACK_SIZE →
    ∃ k', Runs f o sc ⟨inp ++ rest, alt, vf, k⟩ ⟨out ++ rest, alt, vf, k'⟩ ∧ k' ≤ k + ops

private def Shape : Ty → List Bytes → Prop
  | .B, out => ∃ v, out = [v] ∧ GoodVal v
  | .V, out => out = []
  | .K, out => ∃ key sig, out = [key, sig]
  | .W, out => ∃ v, out = [v] ∧ GoodVal v

private def RunShape (f : Flags) (o : Oracle) (m : Ms) : Ty → List Bytes → List Bytes → Prop
  | .W, w, out => ∃ v, out = [v] ∧
      ((∀ x, RunSpec f o (compile m) (x :: w) [v, x] (opsMax m) (size m)) ∨
       (∀ x, RunSpec f o (compile m) (x :: w) [x, v] (opsMax m) (size m)))
  | .B, w, out => RunSpec f o (compile m) w out (opsMax m) (size m)
  | .V, w, out => RunSpec f o (compile m) w out (opsMax m) (size m)
  | .K, w, out => RunSpec f o (compile m) w out (opsMax m) (size m)

private def Spec (f : Flags) (o : Oracle) (m : Ms) (ty : Ty) (w out : List Bytes) : Prop :=
  Shape ty out ∧ RunShape f o m ty w out

private theorem spec_ne {f : Flags} {o : Oracle} {m : Ms} {ty : Ty} {w out : List Bytes} (hne : ty ≠ .W)
    (h : Spec f o m ty w out) : Shape ty out ∧ RunSpec f o (compile m) w out (opsMax m) (size m) := by
  cases ty
  · exact h
  · exact h
  · exact h
  · exact absurd rfl hne

private theorem spec_of_ne {f : Flags} {o : Oracle} {m : Ms} {ty : Ty} {w out : List Bytes} (hne : ty ≠ .W)
    (hs : Shape ty out) (hr : RunSpec f o (compile m) w out (opsMax m) (size m)) : Spec f o m ty w out := by
  cases ty
  · exact ⟨hs, hr⟩
  · exact ⟨hs, hr⟩
  · exact ⟨hs, hr⟩
  · exact absurd rfl hne

private theorem spec_B {f : Flags} {o : Oracle} {m : Ms} {w out : List Bytes} (h : Spec f o m .B w out) :
    ∃ v, out = [v] ∧ GoodVal v ∧ RunSpec f o (compile m) w [v] (opsMax m) (size m) := by
  obtain ⟨⟨v, rfl, hg⟩, hr⟩ := h
  exact ⟨v, rfl, hg, hr⟩

private theorem spec_V {f : Flags} {o : Oracle} {m : Ms} {w out : List Bytes} (h : Spec f o m .V w out) :
    out = [] ∧ RunSpec f o (compile m) w [] (opsMax m) (size m) := by
  obtain ⟨rfl, hr⟩ := h
  exact ⟨rfl, hr⟩

private theorem spec_K {f : Flags} {o : Oracle} {m : Ms} {w out : List Bytes} (h : Spec f o m .K w out) :
    RunSpec f o (compile m) w out (opsMax m) (size m) := h.2

private theorem shape_len {ty : Ty} {out : List Bytes} (h : Shape ty out) : out.length ≤ 2 := by
  cases ty
  · obtain ⟨v, rfl, -⟩ := h; simp
  · rw [h]; simp
  · obtain ⟨key, sig, rfl⟩ := h; simp
  · obtain ⟨v, rfl, -⟩ := h; simp

private theorem spec_W {f : Flags} {o : Oracle} {m : Ms} {w out : List Bytes} (h : Spec f o m .W w out) :
    ∃ v, out = [v] ∧ GoodVal v ∧
      ((∀ x, RunSpec f o (compile m) (x :: w) [v, x] (opsMax m) (size m)) ∨
       (∀ x, RunSpec f o (compile m) (x :: w) [x, v] (opsMax m) (size m))) := by
  obtain ⟨⟨v, rfl, hg⟩, v', hv', hr⟩ := h
  cases hv'
  exact ⟨v, rfl, hg, hr⟩

private theorem spec_B_intro {f : Flags} {o : Oracle} {m : Ms} {w : List Bytes} (v : Bytes) (hg : GoodVal v)
    (hr : RunSpec f o (compile m) w [v] (opsMax m) (size m)) : Spec f o m .B w [v] :=
  ⟨⟨v, rfl, hg⟩, hr⟩

private theorem spec_V_intro {f : Flags} {o : Oracle} {m : Ms} {w : List Bytes}
    (hr : RunSpec f o (compile m) w [] (opsMax m) (size m)) : Spec f o m .V w [] :=
  ⟨rfl, hr⟩

private theorem spec_K_intro {f : Flags} {o : Oracle} {m : Ms} {w : List Bytes} (key sig : Bytes)
    (hr : RunSpec f o (compile m) w [key, sig] (opsMax m) (size m)) : Spec f o m .K w [key, sig] :=
  ⟨⟨key, sig, rfl⟩, hr⟩

private theorem spec_W_intro {f : Flags} {o : Oracle} {m : Ms} {w : List Bytes} (v : Bytes) (hg : GoodVal v)
    (hr : (∀ x, RunSpec f o (compile m) (x :: w) [v, x] (opsMax m) (size m)) ∨
      (∀ x, RunSpec f o (compile m) (x :: w) [x, v] (opsMax m) (size m))) : Spec f o m .W w [v] :=
  ⟨⟨v, rfl, hg⟩, v, rfl, hr⟩

private theorem castToBool_one : castToBool [1] = true := by decide

private theorem castToBool_nil : castToBool [] = false := by decide

/-- The hash fragments share one script shape. -/
private theorem hash_run (f : Flags) (o : Oracle) (c : BitcoinScript.Byte) (hf : Bytes → Bytes) (h pre : Bytes)
    (hlen : pre.length = 32) (hh : h.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hstep : ∀ (b : Bytes) (st alt : List Bytes) (vf : List Bool) (k : Nat), allTrue vf = true →
      k + 1 ≤ MAX_OPS_PER_SCRIPT → st.length + 1 + alt.length ≤ MAX_STACK_SIZE →
      step f o ⟨b :: st, alt, vf, k⟩ (.op c) = some ⟨hf b :: st, alt, vf, k + 1⟩) :
    RunSpec f o ([.op OP_SIZE] ++ [numInstr 32] ++ [.op OP_EQUALVERIFY] ++ [.op c] ++ [.push h] ++ [.op OP_EQUAL])
      [pre] [boolBytes (decide (hf pre = h))] 4 6 := by
  intro rest alt vf k hvf hk hsz
  simp only [List.length_singleton] at hsz
  refine ⟨k + 4, ?_, by omega⟩
  have heq : serialize (pre.length : Int) = serialize 32 := by rw [hlen]; rfl
  exact runs_app (runs_app (runs_app (runs_app (runs_app
    (runs_one (sSize f o pre rest alt vf k hvf (by omega) (by omega)))
    (runs_one (sNum f o _ alt vf (k + 1) 32 hvf ser32_len (by simp only [List.length_cons]; omega))))
    (runs_one (sEqualVerify f o _ _ _ alt vf (k + 1) hvf (by omega) (by simp only [List.length_cons]; omega) heq)))
    (runs_one (hstep pre rest alt vf (k + 2) hvf (by omega) (by omega))))
    (runs_one (sPush f o _ alt vf (k + 3) h hvf hh (by simp only [List.length_cons]; omega))))
    (runs_one (sEqual f o h (hf pre) rest alt vf (k + 3) hvf (by omega) (by omega)))

private theorem sound_of_hasType (f : Flags) (o : Oracle) {m : Ms} {ty : Ty} (ht : HasType m ty) :
    ∀ (w out : List Bytes), Sem f o m w out → Spec f o m ty w out := by
  induction ht with
  | pk_k key hkey =>
    intro w out hs
    obtain ⟨sig, rfl, rfl⟩ := hs
    apply spec_K_intro key sig
    intro rest alt vf k hvf hk hsz
    simp only [List.length_singleton, size] at hsz
    exact ⟨k, runs_one (sPush f o _ alt vf k key hvf hkey (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))), by simp [opsMax]⟩
  | pk_h hh hlen =>
    intro w out hs
    obtain ⟨key, sig, rfl, hhash, rfl⟩ := hs
    apply spec_K_intro key sig
    intro rest alt vf k hvf hk hsz
    simp only [List.length_cons, List.length_nil, size, opsMax] at hsz hk
    refine ⟨k + 3, ?_, by simp [opsMax]⟩
    exact runs_app (runs_app (runs_app
      (runs_one (sDup f o key (sig :: rest) alt vf k hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))))
      (runs_one (sHash160 f o key (key :: sig :: rest) alt vf (k + 1) hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))))
      (runs_one (sPush f o _ alt vf (k + 2) hh hvf hlen (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))))
      (runs_one (sEqualVerify f o hh (o.hash160 key) (key :: sig :: rest) alt vf (k + 2) hvf (by omega)
        (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))) hhash))
  | older n h1 h2 =>
    intro w out hs
    obtain ⟨rfl, hp, rfl⟩ := hs
    apply spec_B_intro _ ⟨n, by omega, h2, rfl⟩
    intro rest alt vf k hvf hk hsz
    simp only [List.length_nil, size, opsMax] at hsz hk
    refine ⟨k + 1, ?_, by simp [opsMax]⟩
    exact runs_app (runs_one (sNum f o rest alt vf k n hvf (ser_len_small n (by omega) h2) (by omega)))
      (runs_one (sCsv f o n rest alt vf k hvf (by omega) (by omega) (by omega) hp))
  | after n h1 h2 =>
    intro w out hs
    obtain ⟨rfl, hp, rfl⟩ := hs
    apply spec_B_intro _ ⟨n, by omega, h2, rfl⟩
    intro rest alt vf k hvf hk hsz
    simp only [List.length_nil, size, opsMax] at hsz hk
    refine ⟨k + 1, ?_, by simp [opsMax]⟩
    exact runs_app (runs_one (sNum f o rest alt vf k n hvf (ser_len_small n (by omega) h2) (by omega)))
      (runs_one (sCltv f o n rest alt vf k hvf (by omega) (by omega) (by omega) hp))
  | sha256 hh hlen =>
    intro w out hs
    obtain ⟨pre, rfl, hpre, rfl⟩ := hs
    exact spec_B_intro _ (goodVal_bool _) (hash_run f o OP_SHA256 o.sha256 hh pre hpre hlen (sSha256 f o))
  | hash256 hh hlen =>
    intro w out hs
    obtain ⟨pre, rfl, hpre, rfl⟩ := hs
    exact spec_B_intro _ (goodVal_bool _) (hash_run f o OP_HASH256 o.hash256 hh pre hpre hlen (sHash256 f o))
  | ripemd160 hh hlen =>
    intro w out hs
    obtain ⟨pre, rfl, hpre, rfl⟩ := hs
    exact spec_B_intro _ (goodVal_bool _) (hash_run f o OP_RIPEMD160 o.ripemd160 hh pre hpre hlen (sRipemd160 f o))
  | hash160 hh hlen =>
    intro w out hs
    obtain ⟨pre, rfl, hpre, rfl⟩ := hs
    exact spec_B_intro _ (goodVal_bool _) (hash_run f o OP_HASH160 o.hash160 hh pre hpre hlen (sHash160 f o))
  | and_v hx hy hne ihx ihy =>
    intro w out hs
    obtain ⟨wx, wy, rfl, hsx, hsy⟩ := hs
    obtain ⟨-, hrx⟩ := spec_V (ihx wx [] hsx)
    obtain ⟨hshape, hry⟩ := spec_ne hne (ihy wy out hsy)
    apply spec_of_ne hne hshape
    intro rest alt vf k hvf hk hsz
    simp only [opsMax, size, List.length_append] at hk hsz ⊢
    obtain ⟨k1, h1, hk1⟩ := hrx (wy ++ rest) alt vf k hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
    obtain ⟨k2, h2, hk2⟩ := hry rest alt vf k1 hvf (by omega) (by omega)
    refine ⟨k2, ?_, by omega⟩
    simp only [compile]
    exact runs_app (runs_assoc h1) h2
  | and_b hx hy ihx ihy =>
    intro w out hs
    obtain ⟨wx, wy, vx, vy, rfl, hsx, hsy, rfl⟩ := hs
    obtain ⟨v, hv, hgx, hrx⟩ := spec_B (ihx wx [vx] hsx)
    cases hv
    obtain ⟨v', hv', hgy, hry⟩ := spec_W (ihy wy [vy] hsy)
    cases hv'
    apply spec_B_intro _ (goodVal_bool _)
    intro rest alt vf k hvf hk hsz
    simp only [opsMax, size, List.length_append] at hk hsz ⊢
    obtain ⟨k1, h1, hk1⟩ := hrx (wy ++ rest) alt vf k hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
    simp only [compile]
    rcases hry with hry | hry
    · obtain ⟨k2, h2, hk2⟩ := hry vx rest alt vf k1 hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      have h3 := sBoolAnd f o vy vx rest alt vf k2 _ _ hvf (by omega) (by omega) (goodVal_toNum vy hgy) (goodVal_toNum vx hgx)
      rw [booland_val, Bool.and_comm] at h3
      exact ⟨k2 + 1, runs_app (runs_app (runs_assoc h1) h2) (runs_one h3), by omega⟩
    · obtain ⟨k2, h2, hk2⟩ := hry vx rest alt vf k1 hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      have h3 := sBoolAnd f o vx vy rest alt vf k2 _ _ hvf (by omega) (by omega) (goodVal_toNum vx hgx) (goodVal_toNum vy hgy)
      rw [booland_val] at h3
      exact ⟨k2 + 1, runs_app (runs_app (runs_assoc h1) h2) (runs_one h3), by omega⟩
  | or_b hx hdx hz hdz ihx ihz =>
    intro w out hs
    obtain ⟨wx, wz, vx, vz, rfl, hsx, hsz', rfl⟩ := hs
    obtain ⟨v, hv, hgx, hrx⟩ := spec_B (ihx wx [vx] hsx)
    cases hv
    obtain ⟨v', hv', hgz, hrz⟩ := spec_W (ihz wz [vz] hsz')
    cases hv'
    apply spec_B_intro _ (goodVal_bool _)
    intro rest alt vf k hvf hk hsz
    simp only [opsMax, size, List.length_append] at hk hsz ⊢
    obtain ⟨k1, h1, hk1⟩ := hrx (wz ++ rest) alt vf k hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
    simp only [compile]
    rcases hrz with hrz | hrz
    · obtain ⟨k2, h2, hk2⟩ := hrz vx rest alt vf k1 hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      have h3 := sBoolOr f o vz vx rest alt vf k2 _ _ hvf (by omega) (by omega) (goodVal_toNum vz hgz) (goodVal_toNum vx hgx)
      rw [boolor_val, Bool.or_comm] at h3
      exact ⟨k2 + 1, runs_app (runs_app (runs_assoc h1) h2) (runs_one h3), by omega⟩
    · obtain ⟨k2, h2, hk2⟩ := hrz vx rest alt vf k1 hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      have h3 := sBoolOr f o vx vz rest alt vf k2 _ _ hvf (by omega) (by omega) (goodVal_toNum vx hgx) (goodVal_toNum vz hgz)
      rw [boolor_val] at h3
      exact ⟨k2 + 1, runs_app (runs_app (runs_assoc h1) h2) (runs_one h3), by omega⟩
  | or_c hx hdx hux hz ihx ihz =>
    intro w out hs
    obtain ⟨rfl, wx, vx, hsx, hs⟩ := hs
    obtain ⟨v, hv, hgx, hrx⟩ := spec_B (ihx wx [vx] hsx)
    cases hv
    apply spec_V_intro
    intro rest alt vf k hvf hk hsz
    simp only [compile]
    rcases hs with ⟨hvx, rfl⟩ | ⟨hvx, wz, rfl, hsz'⟩
    · simp only [opsMax, size, List.length_append] at hk hsz ⊢
      obtain ⟨k1, h1, hk1⟩ := hrx rest alt vf k hvf (by omega) (by omega)
      have h2 := sNotIf f o vx rest alt vf k1 hvf (by omega) (by omega)
      rw [hvx, Bool.not_true] at h2
      obtain ⟨k2, h3, hk2⟩ := skip_of_hasType f o hz rest alt (false :: vf) (k1 + 1) (by rw [allTrue_cons]; simp)
        (by omega) (by omega)
      exact ⟨k2 + 1, runs_app (runs_app (runs_app h1 (runs_one h2)) h3)
        (runs_one (sEndIf f o rest alt false vf k2 (by omega) (by omega))), by omega⟩
    · obtain ⟨-, hrz⟩ := spec_V (ihz wz [] hsz')
      simp only [opsMax, size, List.length_append] at hk hsz ⊢
      obtain ⟨k1, h1, hk1⟩ := hrx (wz ++ rest) alt vf k hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      have h2 := sNotIf f o vx (wz ++ rest) alt vf k1 hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [hvx, Bool.not_false] at h2
      obtain ⟨k2, h3, hk2⟩ := hrz rest alt (true :: vf) (k1 + 1) (by rw [allTrue_cons, hvf]; rfl) (by omega) (by omega)
      exact ⟨k2 + 1, runs_app (runs_app (runs_app (runs_assoc h1) (runs_one h2)) h3)
        (runs_one (sEndIf f o rest alt true vf k2 (by omega) (by omega))), by omega⟩
  | or_d hx hdx hux hz ihx ihz =>
    intro w out hs
    obtain ⟨wx, vx, hsx, hs⟩ := hs
    obtain ⟨v, hv, hgx, hrx⟩ := spec_B (ihx wx [vx] hsx)
    cases hv
    rcases hs with ⟨hvx, rfl, rfl⟩ | ⟨hvx, wz, rfl, hsz'⟩
    · apply spec_B_intro _ hgx
      intro rest alt vf k hvf hk hsz
      simp only [compile, opsMax, size, List.length_append] at hk hsz ⊢
      obtain ⟨k1, h1, hk1⟩ := hrx rest alt vf k hvf (by omega) (by omega)
      have h2 := sIfDupT f o vx rest alt vf k1 hvf (by omega) (by omega) hvx
      have h3 := sNotIf f o vx (vx :: rest) alt vf (k1 + 1) hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [hvx, Bool.not_true] at h3
      obtain ⟨k2, h4, hk2⟩ := skip_of_hasType f o hz (vx :: rest) alt (false :: vf) (k1 + 2) (by rw [allTrue_cons]; simp)
        (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      exact ⟨k2 + 1, runs_app (runs_app (runs_app (runs_app h1 (runs_one h2)) (runs_one h3)) h4)
        (runs_one (sEndIf f o (vx :: rest) alt false vf k2 (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))), by omega⟩
    · obtain ⟨vz, hvz, hgz, hrz⟩ := spec_B (ihz wz out hsz')
      subst hvz
      apply spec_B_intro _ hgz
      intro rest alt vf k hvf hk hsz
      simp only [compile, opsMax, size, List.length_append] at hk hsz ⊢
      obtain ⟨k1, h1, hk1⟩ := hrx (wz ++ rest) alt vf k hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      have h2 := sIfDupF f o vx (wz ++ rest) alt vf k1 hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))) hvx
      have h3 := sNotIf f o vx (wz ++ rest) alt vf (k1 + 1) hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [hvx, Bool.not_false] at h3
      obtain ⟨k2, h4, hk2⟩ := hrz rest alt (true :: vf) (k1 + 2) (by rw [allTrue_cons, hvf]; rfl) (by omega) (by omega)
      exact ⟨k2 + 1, runs_app (runs_app (runs_app (runs_app (runs_assoc h1) (runs_one h2)) (runs_one h3)) h4)
        (runs_one (sEndIf f o (vz :: rest) alt true vf k2 (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))), by omega⟩
  | or_i hx hz hne ihx ihz =>
    intro w out hs
    obtain ⟨b, w', rfl, hs⟩ := hs
    rcases hs with ⟨hb, hsx⟩ | ⟨hb, hsz'⟩
    · obtain ⟨hshape, hrx⟩ := spec_ne hne (ihx w' out hsx)
      have hol := shape_len hshape
      apply spec_of_ne hne hshape
      intro rest alt vf k hvf hk hsz
      simp only [compile, opsMax, size, List.length_cons] at hk hsz ⊢
      have h1 := sIf f o b (w' ++ rest) alt vf k hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [hb] at h1
      obtain ⟨k1, h2, hk1⟩ := hrx rest alt (true :: vf) (k + 1) (by rw [allTrue_cons, hvf]; rfl) (by omega) (by omega)
      have h3 := sElse f o (out ++ rest) alt true vf k1 (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [Bool.not_true] at h3
      obtain ⟨k2, h4, hk2⟩ := skip_of_hasType f o hz (out ++ rest) alt (false :: vf) (k1 + 1) (by rw [allTrue_cons]; simp)
        (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      exact ⟨k2 + 1, runs_app (runs_app (runs_app (runs_app (runs_one h1) h2) (runs_one h3)) h4)
        (runs_one (sEndIf f o (out ++ rest) alt false vf k2 (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))), by omega⟩
    · obtain ⟨hshape, hrz⟩ := spec_ne hne (ihz w' out hsz')
      have hol := shape_len hshape
      apply spec_of_ne hne hshape
      intro rest alt vf k hvf hk hsz
      simp only [compile, opsMax, size, List.length_cons] at hk hsz ⊢
      have h1 := sIf f o b (w' ++ rest) alt vf k hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [hb] at h1
      obtain ⟨k1, h2, hk1⟩ := skip_of_hasType f o hx (w' ++ rest) alt (false :: vf) (k + 1) (by rw [allTrue_cons]; simp)
        (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      have h3 := sElse f o (w' ++ rest) alt false vf k1 (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [Bool.not_false] at h3
      obtain ⟨k2, h4, hk2⟩ := hrz rest alt (true :: vf) (k1 + 1) (by rw [allTrue_cons, hvf]; rfl) (by omega) (by omega)
      exact ⟨k2 + 1, runs_app (runs_app (runs_app (runs_app (runs_one h1) h2) (runs_one h3)) h4)
        (runs_one (sEndIf f o (out ++ rest) alt true vf k2 (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))), by omega⟩
  | andor hx hdx hux hy hz hne ihx ihy ihz =>
    intro w out hs
    obtain ⟨wx, vx, hsx, hs⟩ := hs
    obtain ⟨v, hv, hgx, hrx⟩ := spec_B (ihx wx [vx] hsx)
    cases hv
    rcases hs with ⟨hvx, wy, rfl, hsy⟩ | ⟨hvx, wz, rfl, hsz'⟩
    · obtain ⟨hshape, hry⟩ := spec_ne hne (ihy wy out hsy)
      have hol := shape_len hshape
      apply spec_of_ne hne hshape
      intro rest alt vf k hvf hk hsz
      simp only [compile, opsMax, size, List.length_append] at hk hsz ⊢
      obtain ⟨k1, h1, hk1⟩ := hrx (wy ++ rest) alt vf k hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      have h2 := sNotIf f o vx (wy ++ rest) alt vf k1 hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [hvx, Bool.not_true] at h2
      obtain ⟨k2, h3, hk2⟩ := skip_of_hasType f o hz (wy ++ rest) alt (false :: vf) (k1 + 1) (by rw [allTrue_cons]; simp)
        (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      have h4 := sElse f o (wy ++ rest) alt false vf k2 (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [Bool.not_false] at h4
      obtain ⟨k3, h5, hk3⟩ := hry rest alt (true :: vf) (k2 + 1) (by rw [allTrue_cons, hvf]; rfl) (by omega) (by omega)
      exact ⟨k3 + 1, runs_app (runs_app (runs_app (runs_app (runs_app (runs_assoc h1) (runs_one h2)) h3) (runs_one h4)) h5)
        (runs_one (sEndIf f o (out ++ rest) alt true vf k3 (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))), by omega⟩
    · obtain ⟨hshape, hrz⟩ := spec_ne hne (ihz wz out hsz')
      have hol := shape_len hshape
      apply spec_of_ne hne hshape
      intro rest alt vf k hvf hk hsz
      simp only [compile, opsMax, size, List.length_append] at hk hsz ⊢
      obtain ⟨k1, h1, hk1⟩ := hrx (wz ++ rest) alt vf k hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      have h2 := sNotIf f o vx (wz ++ rest) alt vf k1 hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [hvx, Bool.not_false] at h2
      obtain ⟨k2, h3, hk2⟩ := hrz rest alt (true :: vf) (k1 + 1) (by rw [allTrue_cons, hvf]; rfl) (by omega) (by omega)
      have h4 := sElse f o (out ++ rest) alt true vf k2 (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [Bool.not_true] at h4
      obtain ⟨k3, h5, hk3⟩ := skip_of_hasType f o hy (out ++ rest) alt (false :: vf) (k2 + 1) (by rw [allTrue_cons]; simp)
        (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      exact ⟨k3 + 1, runs_app (runs_app (runs_app (runs_app (runs_app (runs_assoc h1) (runs_one h2)) h3) (runs_one h4)) h5)
        (runs_one (sEndIf f o (out ++ rest) alt false vf k3 (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))), by omega⟩
  | multi kk keys hk1 hk2 hk3 hkeys =>
    intro w out hs
    obtain ⟨sigs, dummy, ok, rfl, hlen, hloop, hdummy, rfl⟩ := hs
    apply spec_B_intro _ (goodVal_bool _)
    intro rest alt vf k hvf hk hsz
    simp only [compile, opsMax, size, List.length_append, List.length_singleton] at hk hsz ⊢
    have hkk : (serialize (kk : Int)).length ≤ MAX_SCRIPT_ELEMENT_SIZE :=
      ser_len_small _ (by omega) (by simp only [MAX_PUBKEYS_PER_MULTISIG] at hk3; omega)
    have hnn : (serialize (keys.length : Int)).length ≤ MAX_SCRIPT_ELEMENT_SIZE :=
      ser_len_small _ (by omega) (by simp only [MAX_PUBKEYS_PER_MULTISIG] at hk3; omega)
    subst hlen
    have e : (sigs ++ [dummy]) ++ rest = sigs ++ dummy :: rest := by simp
    rw [e]
    refine ⟨k + 1 + keys.length, ?_, by omega⟩
    exact runs_app (runs_app (runs_app
      (runs_one (sNum f o _ alt vf k _ hvf hkk (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))))
      (runs_pushes f o keys hkeys _ alt vf k hvf (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))))
      (runs_one (sNum f o _ alt vf k _ hvf hnn (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))))
      (runs_one (sCms f o keys sigs dummy rest alt vf k ok hvf hk3 hk2 (by omega) (by omega) hloop hdummy))
  | wrap_a hx ihx =>
    intro w out hs
    obtain ⟨v, hv, hg, hrx⟩ := spec_B (ihx w out hs)
    subst hv
    apply spec_W_intro _ hg
    right
    intro x rest alt vf k hvf hk hsz
    simp only [compile, opsMax, size, List.length_cons] at hk hsz ⊢
    obtain ⟨k1, h1, hk1⟩ := hrx rest (x :: alt) vf (k + 1) hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
    exact ⟨k1 + 1, runs_app (runs_app
      (runs_one (sToAlt f o x (w ++ rest) alt vf k hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))) h1)
      (runs_one (sFromAlt f o x (v :: rest) alt vf k1 hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))), by omega⟩
  | wrap_s hx hox ihx =>
    intro w out hs
    obtain ⟨v, hv, hg, hrx⟩ := spec_B (ihx w out hs)
    subst hv
    have hlen := (sem_zo f o _ w [v] hs).2 hox
    apply spec_W_intro _ hg
    left
    intro x rest alt vf k hvf hk hsz
    simp only [compile, opsMax, size, List.length_cons] at hk hsz ⊢
    match w, hlen with
    | [w1], _ =>
      obtain ⟨k1, h1, hk1⟩ := hrx (x :: rest) alt vf (k + 1) hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      exact ⟨k1, runs_app
        (runs_one (sSwap f o x w1 rest alt vf k hvf (by omega) (by omega))) h1, by omega⟩
  | wrap_c hx ihx =>
    intro w out hs
    obtain ⟨key, sig, ok, hsx, hcs, rfl⟩ := hs
    have hrx := spec_K (ihx w [key, sig] hsx)
    apply spec_B_intro _ (goodVal_bool _)
    intro rest alt vf k hvf hk hsz
    simp only [compile, opsMax, size] at hk hsz ⊢
    obtain ⟨k1, h1, hk1⟩ := hrx rest alt vf k hvf (by omega) (by omega)
    exact ⟨k1 + 1, runs_app h1
      (runs_one (sCheckSig f o key sig rest alt vf k1 ok hvf (by omega) (by omega) hcs)), by omega⟩
  | wrap_d hx hzx ihx =>
    intro w out hs
    rcases hs with ⟨rfl, hsx, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨-, hrx⟩ := spec_V (ihx [] [] hsx)
      apply spec_B_intro _ goodVal_one
      intro rest alt vf k hvf hk hsz
      simp only [compile, opsMax, size, List.length_singleton] at hk hsz ⊢
      have h1 := sDup f o [1] rest alt vf k hvf (by omega) (by omega)
      have h2 := sIf f o [1] ([1] :: rest) alt vf (k + 1) hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [castToBool_one] at h2
      obtain ⟨k1, h3, hk1⟩ := hrx ([1] :: rest) alt (true :: vf) (k + 2) (by rw [allTrue_cons, hvf]; rfl) (by omega)
        (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      exact ⟨k1 + 1, runs_app (runs_app (runs_app (runs_one h1) (runs_one h2)) h3)
        (runs_one (sEndIf f o ([1] :: rest) alt true vf k1 (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))), by omega⟩
    · apply spec_B_intro _ goodVal_nil
      intro rest alt vf k hvf hk hsz
      simp only [compile, opsMax, size, List.length_singleton] at hk hsz ⊢
      have h1 := sDup f o [] rest alt vf k hvf (by omega) (by omega)
      have h2 := sIf f o [] ([] :: rest) alt vf (k + 1) hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [castToBool_nil] at h2
      obtain ⟨k1, h3, hk1⟩ := skip_of_hasType f o hx ([] :: rest) alt (false :: vf) (k + 2) (by rw [allTrue_cons]; simp)
        (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      exact ⟨k1 + 1, runs_app (runs_app (runs_app (runs_one h1) (runs_one h2)) h3)
        (runs_one (sEndIf f o ([] :: rest) alt false vf k1 (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))), by omega⟩
  | wrap_v hx ihx =>
    intro w out hs
    obtain ⟨v, hsx, hv, rfl⟩ := hs
    obtain ⟨v', hv', hg, hrx⟩ := spec_B (ihx w [v] hsx)
    cases hv'
    apply spec_V_intro
    intro rest alt vf k hvf hk hsz
    simp only [compile, opsMax, size] at hk hsz ⊢
    obtain ⟨k1, h1, hk1⟩ := hrx rest alt vf k hvf (by omega) (by omega)
    exact ⟨k1 + 1, runs_app h1 (runs_one (sVerify f o v rest alt vf k1 hvf (by omega) (by omega) hv)), by omega⟩
  | wrap_j hx hnx ihx =>
    intro w out hs
    rcases hs with ⟨e, w', rfl, hne, helen, hsx⟩ | ⟨rfl, rfl⟩
    · obtain ⟨v, hv, hg, hrx⟩ := spec_B (ihx (e :: w') out hsx)
      subst hv
      apply spec_B_intro _ hg
      intro rest alt vf k hvf hk hsz
      simp only [compile, opsMax, size, List.length_cons] at hk hsz ⊢
      have h1 := sSize f o e (w' ++ rest) alt vf k hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      have h2 := s0NotEqual f o (serialize (e.length : Int)) (e :: (w' ++ rest)) alt vf (k + 1) (e.length : Int) hvf
        (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
        (toNum4_serialize _ (by omega) (by simp only [MAX_SCRIPT_ELEMENT_SIZE] at helen; omega))
      have hne' : (e.length : Int) ≠ 0 := by
        intro h; apply hne; cases e with
        | nil => rfl
        | cons _ _ => simp only [List.length_cons] at h; omega
      rw [if_pos hne', serialize_one] at h2
      have h3 := sIf f o [1] (e :: (w' ++ rest)) alt vf (k + 2) hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [castToBool_one] at h3
      obtain ⟨k1, h4, hk1⟩ := hrx rest alt (true :: vf) (k + 3) (by rw [allTrue_cons, hvf]; rfl) (by omega)
        (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      exact ⟨k1 + 1, runs_app (runs_app (runs_app (runs_app (runs_one h1) (runs_one h2)) (runs_one h3)) h4)
        (runs_one (sEndIf f o (v :: rest) alt true vf k1 (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))), by omega⟩
    · apply spec_B_intro _ goodVal_nil
      intro rest alt vf k hvf hk hsz
      simp only [compile, opsMax, size, List.length_singleton] at hk hsz ⊢
      have h1 := sSize f o [] rest alt vf k hvf (by omega) (by omega)
      have h2 := s0NotEqual f o (serialize (([] : Bytes).length : Int)) ([] :: rest) alt vf (k + 1) 0 hvf
        (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))) (by simp only [List.length_nil, Int.ofNat_zero, serialize_zero]; rfl)
      rw [if_neg (by simp), serialize_zero] at h2
      have h3 := sIf f o [] ([] :: rest) alt vf (k + 2) hvf (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      rw [castToBool_nil] at h3
      obtain ⟨k1, h4, hk1⟩ := skip_of_hasType f o hx ([] :: rest) alt (false :: vf) (k + 3) (by rw [allTrue_cons]; simp)
        (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega)))
      exact ⟨k1 + 1, runs_app (runs_app (runs_app (runs_app (runs_one h1) (runs_one h2)) (runs_one h3)) h4)
        (runs_one (sEndIf f o ([] :: rest) alt false vf k1 (by omega) (by (first | omega | (simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, List.length_reverse]; omega))))), by omega⟩
  | wrap_n hx ihx =>
    intro w out hs
    obtain ⟨v, hsx, rfl⟩ := hs
    obtain ⟨v', hv', hg, hrx⟩ := spec_B (ihx w [v] hsx)
    cases hv'
    apply spec_B_intro _ (goodVal_bool _)
    intro rest alt vf k hvf hk hsz
    simp only [compile, opsMax, size] at hk hsz ⊢
    obtain ⟨k1, h1, hk1⟩ := hrx rest alt vf k hvf (by omega) (by omega)
    have h2 := s0NotEqual f o v rest alt vf k1 _ hvf (by omega) (by omega) (goodVal_toNum v hg)
    rw [notequal_val] at h2
    exact ⟨k1 + 1, runs_app h1 (runs_one h2), by omega⟩

/-- Satisfaction soundness for `B`: a satisfying witness leaves a true value above the untouched stack. -/
theorem solution (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ht : BitcoinMiniscript.HasType m .B) (w rest : List BitcoinScript.Bytes) (hs : BitcoinMiniscript.Sat f o m w)
    (hops : BitcoinMiniscript.opsMax m ≤ BitcoinScript.MAX_OPS_PER_SCRIPT)
    (hsz : w.length + rest.length + BitcoinMiniscript.size m ≤ BitcoinScript.MAX_STACK_SIZE) :
    ∃ v, BitcoinScript.castToBool v = true ∧
      BitcoinScript.evalScript f o (w ++ rest) (BitcoinMiniscript.compile m) = some (v :: rest) := by
  obtain ⟨v, hsem, hv⟩ := hs
  exact ⟨v, hv, BitcoinMiniscript.sem_sound f o m .B ht (by decide) w [v] rest hsem hops hsz⟩
