-- Prove2me | solution 1 for BitcoinScript.p2pkh_correct
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T05:50:53.728935+00:00
-- url     : https://prove2.me/submissions/6b6d460c-eeea-49c2-beb4-2264fc9e35a2

import Definitions.Def_BitcoinScript
import Theorems.Thm_BitcoinScript_eval_pushes

open BitcoinScript

private theorem run_pushes (f : Flags) (o : Oracle) :
    ∀ (ps : List Bytes) (st : List Bytes) (k : Nat),
      (∀ p ∈ ps, p.length ≤ MAX_SCRIPT_ELEMENT_SIZE) → st.length + ps.length ≤ MAX_STACK_SIZE →
      run f o ⟨st, [], [], k⟩ (ps.map Instr.push) = some ⟨ps.reverse ++ st, [], [], k⟩
  | [], st, k, _, _ => by simp [run]
  | p :: ps, st, k, hsz, hlen => by
    simp only [List.map_cons, run, step, allTrue, List.all_nil, ite_true]
    have h1 : ¬ MAX_SCRIPT_ELEMENT_SIZE < p.length := by
      have := hsz p (List.mem_cons_self ..); omega
    simp only [List.length_cons] at hlen
    have h2 : ¬ MAX_STACK_SIZE < (p :: st).length + ([] : List Bytes).length := by
      simp only [List.length_cons, List.length_nil]; omega
    rw [if_neg h1]
    simp only [if_neg h2]
    rw [run_pushes f o ps (p :: st) k (fun q hq => hsz q (List.mem_cons_of_mem _ hq))
      (by simp only [List.length_cons]; omega)]
    simp

private theorem execOp_dup (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_DUP s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := top :: top :: rest } := by
  rfl

private theorem execOp_hash160 (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_HASH160 s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := o.hash160 top :: rest } := by
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

theorem solution (f : Flags) (o : Oracle) (sig pubkey h : Bytes)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pubkey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hh : h.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.verifyScriptPlain f o [.push sig, .push pubkey] (BitcoinScript.p2pkhScript h) = true ↔
      o.hash160 pubkey = h ∧ o.checkSig sig pubkey = some true := by
  unfold verifyScriptPlain
  have h1 : evalScript f o [] [.push sig, .push pubkey] = some [pubkey, sig] := by
    have := BitcoinScript.eval_pushes f o [sig, pubkey] (by simp [hsig, hpk]) (by simp [MAX_STACK_SIZE])
    simpa using this
  rw [h1]
  dsimp only
  unfold p2pkhScript evalScript State.initial
  -- OP_DUP
  rw [run, step_op_small f o _ OP_DUP (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) rfl]
  simp only [execOp_dup, List.length_cons, List.length_nil]
  rw [if_neg (by unfold MAX_STACK_SIZE; omega)]
  dsimp only
  -- OP_HASH160
  rw [run, step_op_small f o _ OP_HASH160 (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) rfl]
  simp only [execOp_hash160, List.length_cons, List.length_nil]
  rw [if_neg (by unfold MAX_STACK_SIZE; omega)]
  dsimp only
  -- push h
  rw [run, step]
  simp only [allTrue, List.all_nil, ite_true]
  rw [if_neg (by omega)]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by unfold MAX_STACK_SIZE; omega)]
  dsimp only
  -- OP_EQUALVERIFY
  rw [run, step_op_small f o _ OP_EQUALVERIFY (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) rfl]
  simp only [execOp_equalverify]
  by_cases heq : o.hash160 pubkey = h
  · simp only [heq, decide_true, ite_true, List.length_cons, List.length_nil]
    rw [if_neg (by unfold MAX_STACK_SIZE; omega)]
    dsimp only
    -- OP_CHECKSIG
    rw [run, step_op_small f o _ OP_CHECKSIG (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) rfl]
    simp only [execOp_checksig]
    cases hcs : o.checkSig sig pubkey with
    | none => simp
    | some ok =>
      simp only [List.length_cons, List.length_nil]
      rw [if_neg (by unfold MAX_STACK_SIZE; omega)]
      dsimp only
      simp only [run, List.isEmpty_nil, ite_true, Option.map_some, castToBool_boolBytes]
      cases ok <;> simp
  · simp only [heq, decide_false, Bool.false_eq_true, ite_false]
    simp [heq]
