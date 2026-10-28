-- Prove2me | solution 2 for BitcoinVerify.p2sh_correct
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:57:24.503397+00:00
-- url     : https://prove2.me/submissions/68c0d7ab-3af4-4404-8078-351df9e295b9

import Definitions.Def_BitcoinVerify
import Theorems.Thm_BitcoinSig_parseScript_p2pkh
import Theorems.Thm_BitcoinScript_eval_pushes
import Theorems.Thm_BitcoinSer_sha256_length
import Theorems.Thm_BitcoinSer_hash160_length
import Theorems.Thm_BitcoinVerify_isPayToScriptHash_iff
import Theorems.Thm_BitcoinVerify_isPushOnly_pushes
import Theorems.Thm_BitcoinVerify_parseScript_pushes

open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

private theorem getD_app_lt {α : Type} (a b : List α) (i : Nat) (d : α) (h : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_app_ge {α : Type} (a b : List α) (i : Nat) (d : α) (h : a.length ≤ i) :
    (a ++ b).getD i d = b.getD (i - a.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private theorem ofNat_toNat' (b : Byte) : BitVec.ofNat 8 b.toNat = b := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem pushBytes_short (d : Bytes) (hd : d.length < 76) : pushBytes d = BitVec.ofNat 8 d.length :: d := by
  unfold pushBytes OP_PUSHDATA1; rw [if_pos hd]

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

private theorem pushBytes_len_pos (d : Bytes) : 1 ≤ (pushBytes d).length := by
  unfold pushBytes
  by_cases h1 : d.length < OP_PUSHDATA1
  · rw [if_pos h1]; simp
  · rw [if_neg h1]
    by_cases h2 : d.length ≤ 0xff
    · rw [if_pos h2]; simp
    · rw [if_neg h2]; split <;> simp

private theorem pushesBytes_cons_ne_nil (p : Bytes) (ps : List Bytes) : pushesBytes (p :: ps) ≠ [] := by
  intro h
  have := congrArg List.length h
  simp only [pushesBytes, List.flatMap_cons, List.length_append, List.length_nil] at this
  have := pushBytes_len_pos p
  omega

private theorem parseScriptAux_nil (fuel : Nat) : parseScriptAux fuel [] = some [] := by
  cases fuel <;> rfl

private theorem parseScriptAux_cons (fuel : Nat) (s : Bytes) (hs : s ≠ []) :
    parseScriptAux (fuel + 1) s =
      match getOp s with
      | none => none
      | some (i, r) =>
        match parseScriptAux fuel r with
        | none => none
        | some is => some (i :: is) := by
  cases s with
  | nil => exact absurd rfl hs
  | cons b bs => rfl

private theorem isPushOnlyAux_cons (fuel : Nat) (s : Bytes) (hs : s ≠ []) :
    isPushOnlyAux (fuel + 1) s =
      match getOp s with
      | none => false
      | some (.push _, r) => isPushOnlyAux fuel r
      | some (.op c, r) => if BitcoinScript.OP_16 < c then false else isPushOnlyAux fuel r := by
  cases s with
  | nil => exact absurd rfl hs
  | cons b bs => rfl

private theorem parseScriptAux_pushes : ∀ (ps : List Bytes) (fuel : Nat), ps.length ≤ fuel →
    (∀ p ∈ ps, p.length ≤ MAX_SCRIPT_ELEMENT_SIZE) →
    parseScriptAux fuel (pushesBytes ps) = some (ps.map Instr.push)
  | [], fuel, _, _ => by cases fuel <;> rfl
  | p :: ps, fuel, hf, hp => by
    simp only [List.length_cons] at hf
    match fuel, hf with
    | f + 1, hf =>
      rw [parseScriptAux_cons _ _ (pushesBytes_cons_ne_nil p ps)]
      simp only [pushesBytes, List.flatMap_cons]
      rw [getOp_pushBytes p _ (hp p (List.mem_cons_self ..))]
      dsimp only
      have := parseScriptAux_pushes ps f (by omega) (fun q hq => hp q (List.mem_cons_of_mem _ hq))
      simp only [pushesBytes] at this
      rw [this]
      rfl

private theorem pushesBytes_length_ge (ps : List Bytes) : ps.length ≤ (pushesBytes ps).length := by
  induction ps with
  | nil => simp [pushesBytes]
  | cons p ps ih =>
    simp only [pushesBytes, List.flatMap_cons, List.length_append, List.length_cons] at *
    have := pushBytes_len_pos p
    omega

private theorem isPushOnlyAux_pushes : ∀ (ps : List Bytes) (fuel : Nat), ps.length ≤ fuel →
    (∀ p ∈ ps, p.length ≤ MAX_SCRIPT_ELEMENT_SIZE) → isPushOnlyAux fuel (pushesBytes ps) = true
  | [], fuel, _, _ => by cases fuel <;> rfl
  | p :: ps, fuel, hf, hp => by
    simp only [List.length_cons] at hf
    match fuel, hf with
    | f + 1, hf =>
      rw [isPushOnlyAux_cons _ _ (pushesBytes_cons_ne_nil p ps)]
      simp only [pushesBytes, List.flatMap_cons]
      rw [getOp_pushBytes p _ (hp p (List.mem_cons_self ..))]
      have := isPushOnlyAux_pushes ps f (by omega) (fun q hq => hp q (List.mem_cons_of_mem _ hq))
      simp only [pushesBytes] at this
      exact this

private theorem execOp_dup (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_DUP s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := top :: top :: rest } := by rfl

private theorem execOp_hash160 (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_HASH160 s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := o.hash160 top :: rest } := by rfl

private theorem execOp_equalverify (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_EQUALVERIFY s = match s.stack with
      | a :: b :: rest => if decide (b = a) then some { s with stack := rest } else none
      | _ => none := by rfl

private theorem execOp_equal (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_EQUAL s = match s.stack with
      | a :: b :: rest => some { s with stack := boolBytes (decide (b = a)) :: rest }
      | _ => none := by rfl

private theorem execOp_checksig (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_CHECKSIG s = match s.stack with
      | pubkey :: sig :: rest =>
        match o.checkSig sig pubkey with
        | none => none
        | some ok => some { s with stack := boolBytes ok :: rest }
      | _ => none := by rfl

private theorem castToBool_boolBytes (b : Bool) : castToBool (boolBytes b) = b := by
  cases b <;> rfl

private theorem step_op_small (f : Flags) (o : Oracle) (s : State) (c : Byte)
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

/-- The P2PKH script on a stack `pk :: sig :: rest` (top first). -/
private theorem run_p2pkh (f : Flags) (o : Oracle) (pk sig h : Bytes) (rest : List Bytes)
    (hh : h.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hr : rest.length + 4 ≤ MAX_STACK_SIZE) :
    evalScript f o (pk :: sig :: rest) (p2pkhScript h) =
      if o.hash160 pk = h then
        (match o.checkSig sig pk with
         | none => none
         | some ok => some (boolBytes ok :: rest))
      else none := by
  unfold p2pkhScript evalScript State.initial
  rw [run, step_op_small f o _ OP_DUP (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) rfl]
  simp only [execOp_dup, List.length_cons, List.length_nil]
  rw [if_neg (by unfold MAX_STACK_SIZE at *; omega)]
  dsimp only
  rw [run, step_op_small f o _ OP_HASH160 (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) rfl]
  simp only [execOp_hash160, List.length_cons, List.length_nil]
  rw [if_neg (by unfold MAX_STACK_SIZE at *; omega)]
  dsimp only
  rw [run, step]
  simp only [allTrue, List.all_nil, ite_true]
  rw [if_neg (by omega)]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by unfold MAX_STACK_SIZE at *; omega)]
  dsimp only
  rw [run, step_op_small f o _ OP_EQUALVERIFY (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) rfl]
  simp only [execOp_equalverify]
  by_cases heq : o.hash160 pk = h
  · simp only [heq, decide_true, ite_true, List.length_cons, List.length_nil]
    rw [if_neg (by unfold MAX_STACK_SIZE at *; omega)]
    dsimp only
    rw [run, step_op_small f o _ OP_CHECKSIG (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) rfl]
    simp only [execOp_checksig]
    cases hcs : o.checkSig sig pk with
    | none => simp
    | some ok =>
      simp only [List.length_cons, List.length_nil]
      rw [if_neg (by unfold MAX_STACK_SIZE at *; omega)]
      dsimp only
      simp [run]
  · simp [heq]

/-- The P2SH script `OP_HASH160 <h> OP_EQUAL` on a stack `redeem :: rest`. -/
private theorem run_p2sh (f : Flags) (o : Oracle) (redeem h : Bytes) (rest : List Bytes)
    (hh : h.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hr : rest.length + 2 ≤ MAX_STACK_SIZE) :
    evalScript f o (redeem :: rest) [.op OP_HASH160, .push h, .op OP_EQUAL] =
      some (boolBytes (decide (o.hash160 redeem = h)) :: rest) := by
  unfold evalScript State.initial
  rw [run, step_op_small f o _ OP_HASH160 (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) rfl]
  simp only [execOp_hash160, List.length_cons, List.length_nil]
  rw [if_neg (by unfold MAX_STACK_SIZE at *; omega)]
  dsimp only
  rw [run, step]
  simp only [allTrue, List.all_nil, ite_true]
  rw [if_neg (by omega)]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by unfold MAX_STACK_SIZE at *; omega)]
  dsimp only
  rw [run, step_op_small f o _ OP_EQUAL (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) rfl]
  simp only [execOp_equal, List.length_cons, List.length_nil]
  rw [if_neg (by unfold MAX_STACK_SIZE at *; omega)]
  dsimp only
  simp [run]

/-- `parseScript (p2shBytes h)`. -/
private theorem parseScript_p2sh (h : Bytes) (hh : h.length = 20) :
    parseScript (p2shBytes h) = some [.op OP_HASH160, .push h, .op OP_EQUAL] := by
  have e : p2shBytes h = 0xa9 :: 0x14 :: (h ++ [0x87]) := by
    unfold p2shBytes; rw [pushBytes_short _ (by rw [hh]; decide)]; rw [hh]; rfl
  rw [e]
  unfold parseScript
  have hl : (0xa9 :: 0x14 :: (h ++ [0x87]) : Bytes).length = 23 := by simp [hh]
  rw [hl]
  have ht : (h ++ [0x87]).take 20 = h := List.take_left' hh
  have hd : (h ++ [0x87]).drop 20 = [0x87] := List.drop_left' hh
  simp [parseScriptAux, getOp, OP_PUSHDATA1, OP_PUSHDATA4, ht, hd, hh]
  decide

/-- `parseScript (witnessBytes v prog)`. -/
private theorem parseScript_witness (v : Nat) (prog : Bytes) (hv : v ≤ 16) (h2 : 2 ≤ prog.length) (h40 : prog.length ≤ 40) :
    parseScript (witnessBytes v prog) =
      some [(if v = 0 then .push [] else .op (BitVec.ofNat 8 (0x50 + v))), .push prog] := by
  unfold witnessBytes
  rw [pushBytes_short _ (by omega)]
  unfold parseScript
  simp only [List.length_cons]
  have hp : getOp (BitVec.ofNat 8 prog.length :: prog) = some (.push prog, []) := by
    have := getOp_pushBytes prog [] (by unfold MAX_SCRIPT_ELEMENT_SIZE; omega)
    rw [pushBytes_short _ (by omega), List.append_nil] at this; exact this
  by_cases h0 : v = 0
  · subst h0
    simp only [ite_true]
    rw [parseScriptAux_cons _ _ (by simp)]
    simp only [getOp, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, OP_PUSHDATA4, OP_PUSHDATA1]
    simp only [show (0:Nat) ≤ 78 from by omega, show (0:Nat) < 76 from by omega, ite_true, List.take_zero,
      List.drop_zero, List.length_cons, show ¬ (prog.length + 1 < 0) from by omega, ite_false]
    rw [parseScriptAux_cons _ _ (by simp), hp]
    simp [parseScriptAux_nil]
  · rw [if_neg h0]
    rw [parseScriptAux_cons _ _ (by simp)]
    have hb : (BitVec.ofNat 8 (0x50 + v)).toNat = 0x50 + v := by
      simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
    simp only [getOp, hb, OP_PUSHDATA4]
    rw [if_neg (by omega)]
    dsimp only
    rw [parseScriptAux_cons _ _ (by simp), hp]
    simp [parseScriptAux_nil, h0]

private theorem execOp_small (f : Flags) (o : Oracle) (s : State) (c : Byte)
    (hc : (c == OP_1NEGATE || (OP_1 ≤ c && c ≤ OP_16)) = true) :
    execOp f o true c s = some (pushNum s ((c.toNat : Int) - ((OP_1.toNat : Int) - 1))) := by
  unfold execOp; rw [if_pos hc]

/-- `OP_n <program>` on the empty stack leaves `[program, n]` (top first). -/
private theorem eval_witnessBytes (c : Ctx) (v : Nat) (prog : Bytes) (hv : v ≤ 16) (h2 : 2 ≤ prog.length)
    (h40 : prog.length ≤ 40) :
    evalBytes c .base [] (witnessBytes v prog) =
      some [prog, if v = 0 then [] else serialize (v : Int)] := by
  unfold evalBytes
  rw [if_neg (by unfold witnessBytes MAX_SCRIPT_SIZE; rw [pushBytes_short _ (by omega)]; simp; omega)]
  rw [parseScript_witness v prog hv h2 h40]
  dsimp only
  unfold evalScript State.initial
  by_cases h0 : v = 0
  · subst h0
    simp only [ite_true]
    rw [run, step]
    simp only [allTrue, List.all_nil, ite_true, List.length_nil]
    rw [if_neg (by unfold MAX_SCRIPT_ELEMENT_SIZE; omega), if_neg (by unfold MAX_STACK_SIZE; simp)]
    dsimp only
    rw [run, step]
    simp only [allTrue, List.all_nil, ite_true, List.length_cons, List.length_nil]
    rw [if_neg (by unfold MAX_SCRIPT_ELEMENT_SIZE; omega), if_neg (by unfold MAX_STACK_SIZE; omega)]
    dsimp only
    simp [run]
  · simp only [h0, ite_false]
    have hb : (BitVec.ofNat 8 (0x50 + v)).toNat = 0x50 + v := by
      simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
    -- the small-integer opcode: not counted, not disabled, executed
    have hc16 : ¬ (OP_16 < BitVec.ofNat 8 (0x50 + v)) := by
      rw [BitVec.lt_def, hb]; show ¬ ((96:Nat) < 0x50 + v); omega
    have hdis : isDisabled (BitVec.ofNat 8 (0x50 + v)) = false := by
      have : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨ v = 12 ∨
          v = 13 ∨ v = 14 ∨ v = 15 ∨ v = 16 := by omega
      rcases this with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide
    have hsmall : (BitVec.ofNat 8 (0x50 + v) == OP_1NEGATE || (OP_1 ≤ BitVec.ofNat 8 (0x50 + v) &&
        BitVec.ofNat 8 (0x50 + v) ≤ OP_16)) = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, BitVec.le_def, hb, OP_1, OP_16]
      right; constructor <;> simp <;> omega
    rw [run, step]
    simp only [allTrue, List.all_nil, ite_true, hdis, Bool.false_eq_true, ite_false, Bool.true_or]
    rw [show decide (OP_16 < BitVec.ofNat 8 (0x50 + v)) = false from decide_eq_false hc16]
    simp only [Bool.false_and, Bool.false_eq_true, ite_false]
    rw [execOp_small _ _ _ _ hsmall]
    simp only [pushNum, List.length_cons, List.length_nil]
    have hst : ¬ (MAX_STACK_SIZE < 0 + 1 + 0) := by unfold MAX_STACK_SIZE; omega
    simp only [hst, ite_false]
    rw [run, step]
    simp only [allTrue, List.all_nil, ite_true, List.length_cons, List.length_nil]
    rw [if_neg (by unfold MAX_SCRIPT_ELEMENT_SIZE; omega), if_neg (by unfold MAX_STACK_SIZE; omega)]
    dsimp only
    simp only [run, List.isEmpty_nil, ite_true, Option.map_some, Option.some.injEq, List.cons.injEq, true_and,
      and_true]
    rw [hb]; congr 1; unfold OP_1; simp; omega

/-- The P2SH output script on the empty stack-of-pushes. -/
private theorem eval_pushes_bytes (c : Ctx) (v : SigVersion) (ps : List Bytes)
    (hp : ∀ p ∈ ps, p.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hn : ps.length ≤ MAX_STACK_SIZE)
    (hsz : (pushesBytes ps).length ≤ MAX_SCRIPT_SIZE) :
    evalBytes c v [] (pushesBytes ps) = some ps.reverse := by
  unfold evalBytes
  rw [if_neg (by omega), BitcoinVerify.parseScript_pushes ps hp]
  exact BitcoinScript.eval_pushes _ _ ps hp hn

/-- **P2SH is correct** (non-witness redeem script, no witness). With the P2SH flag, the output
`OP_HASH160 <h> OP_EQUAL` spent with the push-only scriptSig `<a₁> … <aₖ> <redeem>` verifies iff
`Hash160(redeem) = h` and `redeem`, run on the stack of the pushed arguments, leaves a true top. -/
theorem solution (tap : TaprootHandler) (c : Ctx) (args : List Bytes) (redeem h : Bytes)
    (hp : c.flags.p2sh = true) (hh : h.length = 20)
    (hargs : ∀ a ∈ args, a.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hred : redeem.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hn : args.length + 2 ≤ BitcoinScript.MAX_STACK_SIZE)
    (hsz : (BitcoinVerify.pushesBytes (args ++ [redeem])).length ≤ BitcoinVerify.MAX_SCRIPT_SIZE)
    (hnw : BitcoinVerify.isWitnessProgram redeem = none) :
    BitcoinVerify.verifyScript tap c (BitcoinVerify.pushesBytes (args ++ [redeem])) (BitcoinVerify.p2shBytes h) [] = true ↔
      BitcoinSer.hash160 redeem = h ∧
      ∃ st, BitcoinVerify.evalBytes c .base args.reverse redeem = some st ∧ BitcoinVerify.topTrue st = true := by
  have hall : ∀ a ∈ args ++ [redeem], a.length ≤ MAX_SCRIPT_ELEMENT_SIZE := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hargs a ha
    · simp at ha; subst ha; exact hred
  have hsig : evalBytes c .base [] (pushesBytes (args ++ [redeem])) = some (redeem :: args.reverse) := by
    rw [eval_pushes_bytes c .base _ hall (by simp; omega) hsz]; simp
  have hspk : evalBytes c .base (redeem :: args.reverse) (p2shBytes h) =
      some (boolBytes (decide (hash160 redeem = h)) :: args.reverse) := by
    unfold evalBytes
    rw [if_neg (by unfold p2shBytes MAX_SCRIPT_SIZE; rw [pushBytes_short _ (by omega)]; simp; omega)]
    rw [parseScript_p2sh h hh]
    dsimp only
    rw [run_p2sh _ _ redeem h args.reverse (by unfold MAX_SCRIPT_ELEMENT_SIZE; omega) (by simp; omega)]
    rfl
  have hp2sh : isPayToScriptHash (p2shBytes h) = true := (BitcoinVerify.isPayToScriptHash_iff _).2 ⟨h, hh, rfl⟩
  have hnwp : isWitnessProgram (p2shBytes h) = none := by
    unfold isWitnessProgram p2shBytes
    rw [pushBytes_short _ (by omega)]
    simp only [List.singleton_append, List.length_cons, List.length_append, List.length_nil, hh,
      List.getD_cons_zero]
    rw [if_neg (by omega)]
    (try dsimp only)
    rw [if_pos (by simp)]
  have hpush : isPushOnly (pushesBytes (args ++ [redeem])) = true := BitcoinVerify.isPushOnly_pushes _ hall
  have ht : topTrue (boolBytes (decide (hash160 redeem = h)) :: args.reverse) = decide (hash160 redeem = h) :=
    castToBool_boolBytes _
  unfold verifyScript
  rw [hsig]; (try dsimp only)
  rw [hspk]; (try dsimp only)
  simp only [ht, hnwp, hp, hp2sh, Bool.true_and, hpush, Bool.not_true, Bool.false_eq_true, ite_false]
  by_cases heq : hash160 redeem = h
  · simp only [heq, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, true_and]
    cases c.flags.witness <;> (try simp only [Bool.false_eq_true, ite_false, ite_true])
    · cases hev : evalBytes c .base args.reverse redeem with
      | none => simp
      | some st =>
        simp only [hnw, List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
        cases ht' : topTrue st <;> simp [ht']
    · cases hev : evalBytes c .base args.reverse redeem with
      | none => simp
      | some st =>
        simp only [hnw]
        cases ht' : topTrue st <;> simp [ht']
  · simp [heq]
