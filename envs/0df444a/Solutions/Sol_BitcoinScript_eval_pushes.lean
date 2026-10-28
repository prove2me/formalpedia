-- Prove2me | solution 1 for BitcoinScript.eval_pushes
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T05:49:29.494183+00:00
-- url     : https://prove2.me/submissions/f1d0c72f-1540-42f8-9ef3-343c346ce55b

import Definitions.Def_BitcoinScript

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

theorem solution (f : Flags) (o : Oracle) (ps : List Bytes)
    (hsz : ∀ p ∈ ps, p.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hlen : ps.length ≤ BitcoinScript.MAX_STACK_SIZE) :
    BitcoinScript.evalScript f o [] (ps.map Instr.push) = some ps.reverse := by
  unfold evalScript State.initial
  rw [run_pushes f o ps [] 0 hsz (by simpa using hlen)]
  simp
