-- Prove2me | solution 1 for BitcoinVerify.p2sh_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:42:09.267668+00:00
-- url     : https://prove2.me/submissions/fdb4bfe6-4f62-48e3-a0be-2be2bf4bc542

import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
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

theorem S189B_run_cons (f : Flags) (o : Oracle) (s : State) (i : Instr) (rest : Script) :
    run f o s (i :: rest) = match step f o s i with
      | none => none
      | some s' => run f o s' rest := rfl

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

theorem S189B_s76 (f : Flags) (o : Oracle) (pk sig : Bytes) :
    step f o ⟨[pk, sig], [], [], 0⟩ (.op 0x76) = some ⟨[pk, pk, sig], [], [], 1⟩ := rfl

theorem S189B_sa9 (f : Flags) (o : Oracle) (pk sig : Bytes) :
    step f o ⟨[pk, pk, sig], [], [], 1⟩ (.op 0xa9) = some ⟨[o.hash160 pk, pk, sig], [], [], 2⟩ := rfl

theorem S189B_s88 (f : Flags) (o : Oracle) (pk sig h x : Bytes) :
    step f o ⟨[h, x, pk, sig], [], [], 2⟩ (.op 0x88) = if x = h then some ⟨[pk, sig], [], [], 3⟩ else none := by
  have key : step f o ⟨[h, x, pk, sig], [], [], 2⟩ (.op 0x88) =
    (match (if decide (x = h) = true then some (⟨[pk, sig], [], [], 3⟩ : State) else none) with
      | none => none
      | some s' => if MAX_STACK_SIZE < s'.stack.length + s'.altstack.length then none else some s') := rfl
  rw [key]
  by_cases e : x = h
  · simp [e, MAX_STACK_SIZE]
  · simp [e]

theorem S189B_sac (f : Flags) (o : Oracle) (pk sig : Bytes) :
    step f o ⟨[pk, sig], [], [], 3⟩ (.op 0xac) =
      (match o.checkSig sig pk with | none => none | some ok => some ⟨[boolBytes ok], [], [], 4⟩) := by
  have key : step f o ⟨[pk, sig], [], [], 3⟩ (.op 0xac) =
    (match (match o.checkSig sig pk with | none => none | some ok => some (⟨[boolBytes ok], [], [], 4⟩ : State)) with
      | none => none
      | some s' => if MAX_STACK_SIZE < s'.stack.length + s'.altstack.length then none else some s') := rfl
  rw [key]
  cases o.checkSig sig pk <;> rfl

theorem S189B_p2pkh_eq (h : Bytes) (_hh : h.length = 20) :
    p2pkhBytes h = 0x76 :: 0xa9 :: (pushBytes h ++ 0x88 :: 0xac :: []) := by
  simp [p2pkhBytes]

theorem S189B_exec_p2pkh (c : Ctx) (sig pk h : Bytes) (hh : h.length = 20)
    (hsig : sig.length ≤ 520) (hpk : pk.length ≤ 520) :
    executeWitnessScriptV0 c [pk, sig] (p2pkhBytes h) = true ↔
      hash160 pk = h ∧ checkSigPreTapscript (sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
        (p2pkhBytes h) sig pk = some true := by
  have hl : (p2pkhBytes h).length = 25 := by
    rw [S189B_p2pkh_eq h hh, S189B_pb_small h (by omega)]; simp [hh]
  have hany : [pk, sig].any (fun e => BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE < e.length) = false := by
    simp only [List.any_cons, List.any_nil, MAX_SCRIPT_ELEMENT_SIZE]
    simp [Nat.not_lt.mpr hpk, Nat.not_lt.mpr hsig]
  have hparse : parseScript (p2pkhBytes h) =
      some [.op 0x76, .op 0xa9, .push h, .op 0x88, .op 0xac] := by
    unfold parseScript
    rw [hl]
    conv => lhs; rw [S189B_p2pkh_eq h hh]
    rw [show (25 : Nat) = 24 + 1 from rfl, S189B_P_op _ _ _ (by decide),
      show (24 : Nat) = 23 + 1 from rfl, S189B_P_op _ _ _ (by decide),
      show (23 : Nat) = 22 + 1 from rfl, S189B_P_push _ _ _ (by omega),
      show (22 : Nat) = 21 + 1 from rfl, S189B_P_op _ _ _ (by decide),
      show (21 : Nat) = 20 + 1 from rfl, S189B_P_op _ _ _ (by decide), S189B_P_nil]
    rfl
  unfold executeWitnessScriptV0
  rw [hany]
  simp only [Bool.false_eq_true, if_false]
  unfold evalBytes
  rw [hl, if_neg (by simp [MAX_SCRIPT_SIZE]), hparse]
  dsimp only
  unfold evalScript
  simp only [State.initial]
  rw [S189B_run_step _ _ _ _ _ _ (S189B_s76 _ _ _ _), S189B_run_step _ _ _ _ _ _ (S189B_sa9 _ _ _ _),
    S189B_run_push _ _ _ _ _ (by omega) rfl (by simp)]
  dsimp only
  have e1 : (legacyOracle (sigFlagsOf c.flags) c.tx c.nIn c.amount SigVersion.witnessV0 (p2pkhBytes h)).hash160 pk
    = hash160 pk := rfl
  have e2 : (legacyOracle (sigFlagsOf c.flags) c.tx c.nIn c.amount SigVersion.witnessV0 (p2pkhBytes h)).checkSig sig pk
    = checkSigPreTapscript (sigFlagsOf c.flags) c.tx c.nIn c.amount SigVersion.witnessV0 (p2pkhBytes h) sig pk := rfl
  rw [e1, S189B_run_cons, S189B_s88]
  by_cases e : hash160 pk = h
  · rw [if_pos e]
    dsimp only
    rw [S189B_run_cons, S189B_sac, e2]
    cases checkSigPreTapscript (sigFlagsOf c.flags) c.tx c.nIn c.amount SigVersion.witnessV0 (p2pkhBytes h) sig pk with
    | none => simp
    | some ok =>
      dsimp only
      rw [S189B_run_nil _ _ _ rfl]
      cases ok <;> simp [e, topTrue, boolBytes, vchTrue, vchFalse, castToBool]
  · rw [if_neg e]
    simp [e]

theorem S189B_p2wpkh (tap : TaprootHandler) (c : Ctx) (sig pk h : Bytes)
    (hf : c.flags.witness = true) (hh : h.length = 20)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes 0 h) [sig, pk] = true ↔
      BitcoinScript.castToBool h = true ∧ BitcoinSer.hash160 pk = h ∧
      BitcoinSig.checkSigPreTapscript (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
        (BitcoinSig.p2pkhBytes h) sig pk = some true := by
  unfold verifyScript
  rw [S189B_eval_nil]
  dsimp only
  rw [S189B_eval_wb0 _ _ _ (by omega)]
  dsimp only
  have ht : topTrue [h, []] = castToBool h := rfl
  by_cases hcb : castToBool h = false
  · simp only [ht, hcb]; simp
  · simp only [ht, show castToBool h = true by simpa using hcb]
    simp only [Bool.not_true, Bool.false_eq_true, if_false, hf, if_true,
      S189B_iwp_wb 0 h (by omega) (by omega) (by omega), ne_eq, not_true_eq_false, true_and]
    unfold verifyWitnessProgram
    rw [if_pos rfl, if_neg (by simp [hh, WITNESS_V0_SCRIPTHASH_SIZE]),
      if_pos (by simp [hh, WITNESS_V0_KEYHASH_SIZE]), if_neg (by simp)]
    rw [← S189B_exec_p2pkh c sig pk h hh hsig hpk]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, p2wpkhExec]
    cases executeWitnessScriptV0 c [pk, sig] (p2pkhBytes h) <;> simp

theorem S189B_parse_cons (f : Nat) (s : Bytes) (hs : s ≠ []) :
    parseScriptAux (f + 1) s = match getOp s with
      | none => none
      | some (i, r) => match parseScriptAux f r with
        | none => none
        | some is => some (i :: is) := by
  cases s with
  | nil => exact absurd rfl hs
  | cons a t => rfl

theorem S189B_po_cons (f : Nat) (s : Bytes) (hs : s ≠ []) :
    isPushOnlyAux (f + 1) s = match getOp s with
      | none => false
      | some (.push _, r) => isPushOnlyAux f r
      | some (.op c, r) => if BitcoinScript.OP_16 < c then false else isPushOnlyAux f r := by
  cases s with
  | nil => exact absurd rfl hs
  | cons a t => rfl

theorem S189B_parse_aux (ps : List Bytes) (hp : ∀ p ∈ ps, p.length ≤ 520) :
    ∀ f, (pushesBytes ps).length ≤ f → parseScriptAux f (pushesBytes ps) = some (ps.map Instr.push) := by
  induction ps with
  | nil => intro f _; cases f <;> rfl
  | cons p ps ih =>
    intro f hf
    have e : pushesBytes (p :: ps) = pushBytes p ++ pushesBytes ps := by simp [pushesBytes]
    rw [e] at hf ⊢
    have hl := S189B_pb_len p
    simp only [List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [S189B_parse_cons _ _ (S189B_ne _ _), S189B_getOp_push _ _ (hp p (by simp))]
    simp only
    rw [ih (fun q hq => hp q (by simp [hq])) g (by omega)]
    rfl

theorem S189B_po_aux (ps : List Bytes) (hp : ∀ p ∈ ps, p.length ≤ 520) :
    ∀ f, (pushesBytes ps).length ≤ f → isPushOnlyAux f (pushesBytes ps) = true := by
  induction ps with
  | nil => intro f _; cases f <;> rfl
  | cons p ps ih =>
    intro f hf
    have e : pushesBytes (p :: ps) = pushBytes p ++ pushesBytes ps := by simp [pushesBytes]
    rw [e] at hf ⊢
    have hl := S189B_pb_len p
    simp only [List.length_append] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [S189B_po_cons _ _ (S189B_ne _ _), S189B_getOp_push _ _ (hp p (by simp))]
    exact ih (fun q hq => hp q (by simp [hq])) g (by omega)

theorem S189B_parse_pushes (ps : List Bytes) (hp : ∀ p ∈ ps, p.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinSig.parseScript (BitcoinVerify.pushesBytes ps) = some (ps.map Instr.push) :=
  S189B_parse_aux ps hp _ (Nat.le_refl _)

theorem S189B_po_pushes (ps : List Bytes) (hp : ∀ p ∈ ps, p.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.isPushOnly (BitcoinVerify.pushesBytes ps) = true :=
  S189B_po_aux ps hp _ (Nat.le_refl _)

theorem S189B_p2sh_eq (h : Bytes) (hh : h.length = 20) :
    p2shBytes h = 0xa9 :: 0x14 :: (h ++ [0x87]) := by
  simp [p2shBytes, S189B_pb_small h (by omega), hh]


theorem S189B_step_op (f : Flags) (o : Oracle) (s s' : State) (c : Byte)
    (hv : s.vfExec = []) (hc : OP_16 < c) (hop : s.opCount + 1 ≤ 201) (hd : isDisabled c = false)
    (he : execOp f o true c { s with opCount := s.opCount + 1 } = some s')
    (hsz : s'.stack.length + s'.altstack.length ≤ 1000) :
    step f o s (.op c) = some s' := by
  rw [hv] at he
  have h1 : ¬ (201 < s.opCount + 1) := by omega
  have h2 : ¬ (1000 < s'.stack.length + s'.altstack.length) := by omega
  simp only [step, hv, allTrue, List.all_nil, hc, decide_true, Bool.true_and, MAX_OPS_PER_SCRIPT,
    if_true, hd, Bool.false_eq_true, if_false, Bool.true_or, he, MAX_STACK_SIZE, h1, h2, decide_false]

theorem S189B_run_pushes (f : Flags) (o : Oracle) (ps : List Bytes) (hp : ∀ p ∈ ps, p.length ≤ 520) :
    ∀ s : State, s.vfExec = [] → s.stack.length + s.altstack.length + ps.length ≤ 1000 →
      run f o s (ps.map Instr.push) = run f o { s with stack := ps.reverse ++ s.stack } [] := by
  induction ps with
  | nil => intro s _ _; rfl
  | cons p ps ih =>
    intro s hv hn
    simp only [List.map_cons, List.length_cons] at hn ⊢
    rw [S189B_run_push _ _ _ _ _ (hp p (by simp)) hv (by omega)]
    rw [ih (fun q hq => hp q (by simp [hq])) { s with stack := p :: s.stack } hv (by simp; omega)]
    simp

theorem S189B_eval_pushes (c : Ctx) (sv : SigVersion) (st : List Bytes) (ps : List Bytes)
    (hp : ∀ p ∈ ps, p.length ≤ 520) (hsz : (pushesBytes ps).length ≤ 10000)
    (hn : st.length + ps.length ≤ 1000) :
    evalBytes c sv st (pushesBytes ps) = some (ps.reverse ++ st) := by
  unfold evalBytes
  rw [if_neg (by simp only [MAX_SCRIPT_SIZE]; omega), S189B_parse_pushes ps hp]
  dsimp only
  unfold evalScript
  rw [S189B_run_pushes _ _ _ hp _ rfl (by simp [State.initial]; omega), S189B_run_nil _ _ _ rfl]
  rfl

theorem S189B_p2sh_parse (h : Bytes) (hh : h.length = 20) :
    parseScript (p2shBytes h) = some [.op 0xa9, .push h, .op 0x87] := by
  have hl : (p2shBytes h).length = 23 := by
    rw [S189B_p2sh_eq h hh]; simp [hh]
  unfold parseScript
  rw [hl]
  have e : p2shBytes h = 0xa9 :: (pushBytes h ++ 0x87 :: []) := by simp [p2shBytes]
  rw [e, show (23 : Nat) = 22 + 1 from rfl, S189B_P_op _ _ _ (by decide),
    show (22 : Nat) = 21 + 1 from rfl, S189B_P_push _ _ _ (by omega),
    show (21 : Nat) = 20 + 1 from rfl, S189B_P_op _ _ _ (by decide), S189B_P_nil]
  rfl

theorem S189B_eval_p2sh (c : Ctx) (sv : SigVersion) (h redeem : Bytes) (rest : List Bytes)
    (hh : h.length = 20) (hn : rest.length + 2 ≤ 1000) :
    evalBytes c sv (redeem :: rest) (p2shBytes h) =
      some (boolBytes (decide (hash160 redeem = h)) :: rest) := by
  unfold evalBytes
  rw [if_neg (by rw [S189B_p2sh_eq h hh]; simp [hh, MAX_SCRIPT_SIZE]), S189B_p2sh_parse h hh]
  dsimp only
  unfold evalScript
  simp only [State.initial]
  rw [S189B_run_step _ _ _ ⟨hash160 redeem :: rest, [], [], 1⟩ _ _
    (S189B_step_op _ _ _ _ _ rfl (by decide) (by simp) rfl rfl (by simp; omega))]
  rw [S189B_run_push _ _ _ _ _ (by omega) rfl (by simp; omega)]
  dsimp only
  rw [S189B_run_step _ _ _ ⟨boolBytes (decide (hash160 redeem = h)) :: rest, [], [], 2⟩ _ _
    (S189B_step_op _ _ _ _ _ rfl (by decide) (by simp) rfl rfl (by simp; omega))]
  rw [S189B_run_nil _ _ _ rfl]
  rfl

theorem S189B_p2sh_iff (s : Bytes) :
    BitcoinVerify.isPayToScriptHash s = true ↔ ∃ h : Bytes, h.length = 20 ∧ s = BitcoinVerify.p2shBytes h := by
  constructor
  · intro H
    simp only [isPayToScriptHash, Bool.and_eq_true, decide_eq_true_eq] at H
    obtain ⟨⟨⟨hl, h0⟩, h1⟩, h22⟩ := H
    rcases s with _ | ⟨a0, _ | ⟨a1, t⟩⟩
    · simp at hl
    · simp at hl
    simp only [List.length_cons] at hl
    have ht : t ≠ [] := by intro e; subst e; simp at hl
    obtain ⟨h, l, rfl⟩ : ∃ h l, t = h ++ [l] := ⟨_, _, (List.dropLast_concat_getLast ht).symm⟩
    have hd : h.length = 20 := by simp at hl; omega
    refine ⟨h, hd, ?_⟩
    rw [S189B_p2sh_eq _ hd]
    have ea0 : a0 = 0xa9 := BitVec.eq_of_toNat_eq (by simpa using h0)
    have ea1 : a1 = 0x14 := BitVec.eq_of_toNat_eq (by simpa using h1)
    subst ea0 ea1
    have : (BitVec.ofNat 8 0xa9 :: BitVec.ofNat 8 0x14 :: (h ++ [l])).getD 22 0 = l := by
      simp [List.getD_eq_getElem?_getD, hd]
    rw [show (0xa9 : BitVec 8) = BitVec.ofNat 8 0xa9 from rfl, show (0x14 : BitVec 8) = BitVec.ofNat 8 0x14 from rfl, this] at h22
    have el : l = 0x87 := BitVec.eq_of_toNat_eq (by simpa using h22)
    subst el; rfl
  · rintro ⟨h, hh, rfl⟩
    rw [S189B_p2sh_eq _ hh]
    have : (BitVec.ofNat 8 0xa9 :: BitVec.ofNat 8 0x14 :: (h ++ [(0x87 : BitVec 8)])).getD 22 0 = 0x87 := by
      simp [List.getD_eq_getElem?_getD, hh]
    simp only [isPayToScriptHash, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨by simp [hh], rfl⟩, rfl⟩, ?_⟩
    rw [show (0xa9 : BitVec 8) = BitVec.ofNat 8 0xa9 from rfl, show (0x14 : BitVec 8) = BitVec.ofNat 8 0x14 from rfl, this]
    rfl

theorem S189B_iwp_p2sh (h : Bytes) (hh : h.length = 20) : isWitnessProgram (p2shBytes h) = none := by
  rw [S189B_p2sh_eq h hh]
  unfold isWitnessProgram
  simp [hh]

theorem S189B_p2sh_p2wpkh (tap : TaprootHandler) (c : Ctx) (sig pk h : Bytes)
    (hp : c.flags.p2sh = true) (hf : c.flags.witness = true) (hh : h.length = 20)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.verifyScript tap c (BitcoinSig.pushBytes (BitcoinVerify.witnessBytes 0 h))
        (BitcoinVerify.p2shBytes (BitcoinSer.hash160 (BitcoinVerify.witnessBytes 0 h))) [sig, pk] = true ↔
      BitcoinScript.castToBool h = true ∧ BitcoinSer.hash160 pk = h ∧
      BitcoinSig.checkSigPreTapscript (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
        (BitcoinSig.p2pkhBytes h) sig pk = some true := by
  have hwl : (witnessBytes 0 h).length = 22 := by
    rw [S189B_wb_eq _ _ (by omega)]; simp [hh]
  have hH := S189B_h160 (witnessBytes 0 h)
  have hps : pushBytes (witnessBytes 0 h) = pushesBytes [witnessBytes 0 h] := by simp [pushesBytes]
  have hpsl : (pushesBytes [witnessBytes 0 h]).length = 23 := by
    rw [← hps, S189B_pb_small _ (by omega)]; simp [hwl]
  have hpo : isPushOnly (pushBytes (witnessBytes 0 h)) = true := by
    rw [hps]; exact S189B_po_pushes _ (by simp [hwl, MAX_SCRIPT_ELEMENT_SIZE])
  have hP2 : isPayToScriptHash (p2shBytes (hash160 (witnessBytes 0 h))) = true :=
    (S189B_p2sh_iff _).2 ⟨_, hH, rfl⟩
  unfold verifyScript
  rw [hps, S189B_eval_pushes _ _ _ _ (by simp [hwl]) (by omega) (by simp), ← hps]
  rw [show ([witnessBytes 0 h].reverse ++ [] : List Bytes) = [witnessBytes 0 h] from rfl]
  dsimp only
  rw [S189B_eval_p2sh _ _ _ _ _ hH (by simp)]
  dsimp only
  have ht1 : topTrue [boolBytes true] = true := rfl
  simp only [decide_true, ht1, Bool.not_true, Bool.false_eq_true, if_false, hf, if_true, S189B_iwp_p2sh _ hH, hp, hP2,
    hpo, Bool.true_and]
  rw [S189B_eval_wb0 _ _ _ (by omega)]
  dsimp only
  have ht : topTrue [h, []] = castToBool h := rfl
  by_cases hcb : castToBool h = false
  · simp only [ht, hcb]; simp
  · simp only [ht, show castToBool h = true by simpa using hcb]
    simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true,
      S189B_iwp_wb 0 h (by omega) (by omega) (by omega), ne_eq, not_true_eq_false, true_and]
    unfold verifyWitnessProgram
    rw [if_pos rfl, if_neg (by simp [hh, WITNESS_V0_SCRIPTHASH_SIZE]),
      if_pos (by simp [hh, WITNESS_V0_KEYHASH_SIZE]), if_neg (by simp)]
    rw [← S189B_exec_p2pkh c sig pk h hh hsig hpk]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, p2wpkhExec]

theorem S189B_p2sh_correct (tap : TaprootHandler) (c : Ctx) (args : List Bytes) (redeem h : Bytes)
    (hp : c.flags.p2sh = true) (hh : h.length = 20)
    (hargs : ∀ a ∈ args, a.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hred : redeem.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hn : args.length + 2 ≤ BitcoinScript.MAX_STACK_SIZE)
    (hsz : (BitcoinVerify.pushesBytes (args ++ [redeem])).length ≤ BitcoinVerify.MAX_SCRIPT_SIZE)
    (hnw : BitcoinVerify.isWitnessProgram redeem = none) :
    BitcoinVerify.verifyScript tap c (BitcoinVerify.pushesBytes (args ++ [redeem])) (BitcoinVerify.p2shBytes h) [] = true ↔
      BitcoinSer.hash160 redeem = h ∧
      ∃ st, BitcoinVerify.evalBytes c .base args.reverse redeem = some st ∧ BitcoinVerify.topTrue st = true := by
  have hall : ∀ p ∈ args ++ [redeem], p.length ≤ 520 := by
    intro p hp'
    simp only [List.mem_append, List.mem_singleton] at hp'
    rcases hp' with hp' | rfl
    · exact hargs p hp'
    · exact hred
  simp only [MAX_STACK_SIZE] at hn
  simp only [MAX_SCRIPT_SIZE] at hsz
  have hpo := S189B_po_pushes _ hall
  have hP2 : isPayToScriptHash (p2shBytes h) = true := (S189B_p2sh_iff _).2 ⟨_, hh, rfl⟩
  unfold verifyScript
  rw [S189B_eval_pushes _ _ _ _ hall hsz (by simp; omega)]
  rw [show ((args ++ [redeem]).reverse ++ [] : List Bytes) = redeem :: args.reverse by simp]
  dsimp only
  rw [S189B_eval_p2sh _ _ _ _ _ hh (by simp; omega)]
  dsimp only
  by_cases e : hash160 redeem = h
  · have ht1 : topTrue (boolBytes true :: args.reverse) = true := rfl
    simp only [e, decide_true, ht1, Bool.not_true, Bool.false_eq_true, if_false, S189B_iwp_p2sh _ hh, hp, hP2,
      hpo, Bool.true_and, true_and, Bool.not_true, ite_self]
    cases hw : c.flags.witness
    · simp only [Bool.false_eq_true, if_false]
      cases hev : evalBytes c .base args.reverse redeem with
      | none => simp
      | some st =>
        cases htt : topTrue st <;> simp
    · simp only [if_true, hnw, List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
      cases hev : evalBytes c .base args.reverse redeem with
      | none => simp
      | some st =>
        cases htt : topTrue st <;> simp
  · have ht1 : topTrue (boolBytes false :: args.reverse) = false := rfl
    simp [e, ht1]

open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte
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
  exact S189B_p2sh_correct tap c args redeem h hp hh hargs hred hn hsz hnw
