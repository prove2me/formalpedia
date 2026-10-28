-- Prove2me | solution 1 for BitcoinVerify.p2wsh_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:42:13.735881+00:00
-- url     : https://prove2.me/submissions/dc456f09-1494-45e8-9d5b-d94da0f307cd

import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinScript
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte
theorem S189B_leLen (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

theorem S189B_leVal2 (n : Nat) (h : n < 65536) : leVal (leBytes 2 n) = n := by
  simp [leBytes, leVal, BitVec.toNat_ofNat]; omega

theorem S189B_tn (k : Nat) (h : k < 256) : (BitVec.ofNat 8 k).toNat = k := by
  simp [BitVec.toNat_ofNat]; omega

theorem S189B_getOp_push (d r : Bytes) (hd : d.length ≤ 520) :
    getOp (pushBytes d ++ r) = some (.push d, r) := by
  unfold pushBytes
  by_cases h1 : d.length < OP_PUSHDATA1
  · simp only [h1, if_true, List.cons_append]
    simp only [OP_PUSHDATA1] at h1
    simp [getOp, S189B_tn _ (show d.length < 256 by omega), OP_PUSHDATA4, OP_PUSHDATA1, h1,
      show d.length ≤ 78 by omega]
  · by_cases h2 : d.length ≤ 0xff
    · simp only [h1, h2, if_true, if_false, List.cons_append, List.append_assoc]
      simp only [OP_PUSHDATA1] at h1
      simp [getOp, S189B_tn _ (show d.length < 256 by omega), OP_PUSHDATA4, OP_PUSHDATA1]
    · have h3 : d.length ≤ 0xffff := by omega
      simp only [h1, h2, h3, if_true, if_false, List.cons_append, List.append_assoc]
      simp only [OP_PUSHDATA1] at h1
      simp [getOp, OP_PUSHDATA4, OP_PUSHDATA1, OP_PUSHDATA2, S189B_leLen,
        S189B_leVal2 _ (show d.length < 65536 by omega)]
      rw [if_neg (by omega)]; simp

theorem S189B_pb_len (d : Bytes) : d.length + 1 ≤ (pushBytes d).length := by
  unfold pushBytes; repeat' split
  all_goals simp [S189B_leLen]

theorem S189B_ne (d r : Bytes) : pushBytes d ++ r ≠ [] := by
  intro h
  have h1 := congrArg List.length h
  simp only [List.length_append, List.length_nil] at h1
  have := S189B_pb_len d
  omega

theorem S189B_P_op (f : Nat) (b : Byte) (r : Bytes) (hb : 0x4e < b.toNat) :
    parseScriptAux (f + 1) (b :: r) = (parseScriptAux f r).map (Instr.op b :: ·) := by
  have : getOp (b :: r) = some (.op b, r) := by
    simp only [getOp]; rw [if_neg (show ¬ b.toNat ≤ OP_PUSHDATA4 by simp only [OP_PUSHDATA4]; omega)]
  simp only [parseScriptAux, this]
  cases parseScriptAux f r <;> rfl

theorem S189B_P_push (f : Nat) (d r : Bytes) (hd : d.length ≤ 520) :
    parseScriptAux (f + 1) (pushBytes d ++ r) = (parseScriptAux f r).map (Instr.push d :: ·) := by
  obtain ⟨a, t, e⟩ : ∃ a t, pushBytes d ++ r = a :: t := by
    cases h : pushBytes d ++ r with
    | nil => exact absurd h (S189B_ne d r)
    | cons a t => exact ⟨a, t, rfl⟩
  have g := S189B_getOp_push d r hd
  rw [e] at g ⊢
  simp only [parseScriptAux, g]
  cases parseScriptAux f r <;> rfl

theorem S189B_P_nil (f : Nat) : parseScriptAux f [] = some [] := by cases f <;> rfl

/-- running a push -/
theorem S189B_run_push (f : Flags) (o : Oracle) (s : State) (d : Bytes) (rest : Script)
    (hd : d.length ≤ 520) (hs : s.vfExec = []) (hsz : s.stack.length + s.altstack.length + 1 ≤ 1000) :
    run f o s (.push d :: rest) = run f o { s with stack := d :: s.stack } rest := by
  simp only [run, step, MAX_SCRIPT_ELEMENT_SIZE, hs, allTrue, MAX_STACK_SIZE]
  rw [if_neg (by omega)]
  simp only [List.all_nil, if_true, List.length_cons]
  rw [if_neg (by omega)]

theorem S189B_run_step (f : Flags) (o : Oracle) (s s' : State) (i : Instr) (rest : Script)
    (h : step f o s i = some s') : run f o s (i :: rest) = run f o s' rest := by
  simp only [run, h]

theorem S189B_run_nil (f : Flags) (o : Oracle) (s : State) (hs : s.vfExec = []) :
    run f o s [] = some s := by simp [run, hs]

theorem S189B_wb0 (prog : Bytes) : witnessBytes 0 prog = pushBytes [] ++ (pushBytes prog ++ []) := by
  simp [witnessBytes, pushBytes, OP_PUSHDATA1]

theorem S189B_wbv (v : Nat) (prog : Bytes) (hv : v ≠ 0) :
    witnessBytes v prog = BitVec.ofNat 8 (0x50 + v) :: (pushBytes prog ++ []) := by
  simp [witnessBytes, hv]

theorem S189B_eval_nil (c : Ctx) (sv : SigVersion) (st : List Bytes) : evalBytes c sv st [] = some st := by
  simp [evalBytes, parseScript, S189B_P_nil, evalScript, S189B_run_nil, State.initial]

theorem S189B_eval_wb0 (c : Ctx) (sv : SigVersion) (prog : Bytes) (hp : prog.length ≤ 520) :
    evalBytes c sv [] (witnessBytes 0 prog) = some [prog, []] := by
  have hl : (witnessBytes 0 prog).length ≤ 10000 := by
    rw [S189B_wb0]; unfold pushBytes; repeat' split
    all_goals simp [S189B_leLen] <;> omega
  unfold evalBytes
  rw [if_neg (by simp only [MAX_SCRIPT_SIZE]; omega)]
  unfold parseScript
  obtain ⟨n, hn⟩ : ∃ n, (witnessBytes 0 prog).length = n + 1 + 1 := by
    refine ⟨(witnessBytes 0 prog).length - 2, ?_⟩
    rw [S189B_wb0]; have := S189B_pb_len prog
    have : (pushBytes []).length = 1 := rfl
    simp only [List.length_append, List.length_nil]; omega
  rw [hn, S189B_wb0, S189B_P_push _ _ _ (by simp), S189B_P_push _ _ _ hp, S189B_P_nil]
  simp only [Option.map_some]
  simp only [evalScript, State.initial]
  rw [S189B_run_push _ _ _ _ _ (by simp) rfl (by simp), S189B_run_push _ _ _ _ _ hp rfl (by simp),
    S189B_run_nil _ _ _ rfl]
  rfl

theorem S189B_eval_wbv (c : Ctx) (sv : SigVersion) (v : Nat) (prog : Bytes) (hp : prog.length ≤ 520)
    (hv1 : 1 ≤ v) (hv : v ≤ 16) :
    evalBytes c sv [] (witnessBytes v prog) = some [prog, serialize (v : Int)] := by
  have hl : (witnessBytes v prog).length ≤ 10000 := by
    rw [S189B_wbv _ _ (by omega)]; unfold pushBytes; repeat' split
    all_goals simp [S189B_leLen] <;> omega
  unfold evalBytes
  rw [if_neg (by simp only [MAX_SCRIPT_SIZE]; omega)]
  unfold parseScript
  obtain ⟨n, hn⟩ : ∃ n, (witnessBytes v prog).length = n + 1 + 1 := by
    refine ⟨(witnessBytes v prog).length - 2, ?_⟩
    rw [S189B_wbv _ _ (by omega)]; have := S189B_pb_len prog; simp; omega
  rw [hn, S189B_wbv _ _ (by omega), S189B_P_op _ _ _ (by rw [S189B_tn _ (by omega)]; omega),
    S189B_P_push _ _ _ hp, S189B_P_nil]
  simp only [Option.map_some]
  simp only [evalScript, State.initial]
  have hx : ∀ (f : Flags) (o : Oracle), step f o ⟨[], [], [], 0⟩ (Instr.op (BitVec.ofNat 8 (0x50 + v))) =
      some ⟨[serialize (v : Int)], [], [], 0⟩ := by
    intro f o
    have : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 9 ∨ v = 10 ∨
      v = 11 ∨ v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15 ∨ v = 16 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  rw [S189B_run_step _ _ _ _ _ _ (hx _ _), S189B_run_push _ _ _ _ _ hp rfl (by simp), S189B_run_nil _ _ _ rfl]
  rfl
theorem S189B_pb_small (d : Bytes) (h : d.length < 76) : pushBytes d = BitVec.ofNat 8 d.length :: d := by
  simp [pushBytes, OP_PUSHDATA1, h]

theorem S189B_wb_eq (v : Nat) (prog : Bytes) (hp : prog.length < 76) :
    witnessBytes v prog = BitVec.ofNat 8 (if v = 0 then 0 else 0x50 + v) :: BitVec.ofNat 8 prog.length :: prog := by
  simp [witnessBytes, S189B_pb_small prog hp]

theorem S189B_iwp_wb (v : Nat) (prog : Bytes) (hv : v ≤ 16) (h2 : 2 ≤ prog.length) (h40 : prog.length ≤ 40) :
    isWitnessProgram (witnessBytes v prog) = some (v, prog) := by
  rw [S189B_wb_eq _ _ (by omega)]
  have e0 : (BitVec.ofNat 8 (if v = 0 then 0 else 0x50 + v)).toNat = if v = 0 then 0 else 0x50 + v :=
    S189B_tn _ (by split <;> omega)
  have e1 : (BitVec.ofNat 8 prog.length).toNat = prog.length := S189B_tn _ (by omega)
  unfold isWitnessProgram
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_cons, List.drop_succ_cons,
    List.drop_zero]
  rw [e0, e1]
  rw [if_neg (by omega), if_neg (by split <;> omega), if_pos (by omega)]
  simp only [Option.some.injEq, Prod.mk.injEq, and_true]
  unfold decodeOpN
  split <;> simp_all <;> omega

theorem S189B_uwv (tap : TaprootHandler) (c : Ctx) (v : Nat) (prog : Bytes)
    (w : List Bytes) (hf : c.flags.witness = true) (hv : v ≤ 16)
    (hu : 2 ≤ v ∨ (v = 1 ∧ prog.length ≠ 32)) (h2 : 2 ≤ prog.length) (h40 : prog.length ≤ 40) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes v prog) w = BitcoinScript.castToBool prog := by
  unfold verifyScript
  rw [S189B_eval_nil]
  dsimp only
  rw [S189B_eval_wbv _ _ _ _ (by omega) (by omega) hv]
  dsimp only
  have ht : topTrue [prog, serialize (v : Int)] = castToBool prog := rfl
  by_cases hcb : castToBool prog = false
  · simp only [ht, hcb]; rfl
  · simp only [ht, show castToBool prog = true by simpa using hcb]
    simp only [Bool.not_true, Bool.false_eq_true, if_false, hf, if_true, S189B_iwp_wb v prog hv h2 h40,
      ne_eq, not_true_eq_false]
    unfold verifyWitnessProgram
    rw [if_neg (by omega), if_neg (by simp only [WITNESS_V1_TAPROOT_SIZE]; omega)]
    simp

theorem S189B_sha (m : Bytes) : (sha256 m).length = 32 := by
  simp [sha256, be32Bytes, beBytes, S189B_leLen]

theorem S189B_h160 (m : Bytes) : (hash160 m).length = 20 := by
  simp [hash160, ripemd160, le32Bytes, S189B_leLen]

theorem S189B_p2wsh (tap : TaprootHandler) (c : Ctx) (ws : List Bytes) (script : Bytes)
    (hf : c.flags.witness = true) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 script)) (ws ++ [script]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 script) = true ∧
      BitcoinVerify.executeWitnessScriptV0 c ws.reverse script = true := by
  have hs := S189B_sha script
  unfold verifyScript
  rw [S189B_eval_nil]
  dsimp only
  rw [S189B_eval_wb0 _ _ _ (by omega)]
  dsimp only
  have ht : topTrue [sha256 script, []] = castToBool (sha256 script) := rfl
  by_cases hcb : castToBool (sha256 script) = false
  · simp only [ht, hcb]; simp
  · simp only [ht, show castToBool (sha256 script) = true by simpa using hcb]
    simp only [Bool.not_true, Bool.false_eq_true, if_false, hf, if_true,
      S189B_iwp_wb 0 (sha256 script) (by omega) (by omega) (by omega), ne_eq, not_true_eq_false, true_and]
    unfold verifyWitnessProgram
    simp only [if_true, hs, WITNESS_V0_SCRIPTHASH_SIZE, List.getLast?_concat, List.dropLast_concat,
      ne_eq, not_true_eq_false, if_false]
    cases executeWitnessScriptV0 c ws.reverse script <;> simp

open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte
theorem solution (tap : TaprootHandler) (c : Ctx) (ws : List Bytes) (script : Bytes)
    (hf : c.flags.witness = true) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 script)) (ws ++ [script]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 script) = true ∧
      BitcoinVerify.executeWitnessScriptV0 c ws.reverse script = true := by
  exact S189B_p2wsh tap c ws script hf
