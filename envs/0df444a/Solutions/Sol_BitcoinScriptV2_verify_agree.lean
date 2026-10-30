-- Prove2me | solution 1 for BitcoinScriptV2.verify_agree
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:30:53.152679+00:00
-- url     : https://prove2.me/submissions/b7f12f3c-a9cf-4c7d-83a0-874941347961

import Definitions.Def_BitcoinScriptV2
import Theorems.Thm_BitcoinScriptV2_evalBytes_agree
import Theorems.Thm_BitcoinScriptV2_evalOk_witness
import Theorems.Thm_BitcoinScriptV2_stepV2_agree

open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

set_option linter.unusedSimpArgs false

private theorem annotateAux_parse : ∀ (n : Nat) (s : BitcoinScript.Bytes),
    (annotateAux n s).map (List.map Prod.fst) = parseScriptAux n s
  | _, [] => by cases ‹Nat› <;> simp [annotateAux, parseScriptAux]
  | 0, _ :: _ => by simp [annotateAux, parseScriptAux]
  | n + 1, b :: s => by
    simp only [annotateAux, parseScriptAux]
    cases getOp (b :: s) with
    | none => rfl
    | some ir =>
      obtain ⟨i, r⟩ := ir
      have ih := annotateAux_parse n r
      cases h : annotateAux n r with
      | none => simp only [h, Option.map_none] at ih; simp [h, ← ih]
      | some l => simp only [h, Option.map_some] at ih; simp [h, ← ih]

/-- `getOp` on a non-push opcode consumes exactly one byte. -/
private theorem getOp_op (s r : BitcoinScript.Bytes) (c : BitcoinScript.Byte) (h : getOp s = some (.op c, r)) :
    s = c :: r := by
  cases s with
  | nil => simp [getOp] at h
  | cons b rest =>
    simp only [getOp] at h
    split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
    · simp at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2; rfl

/-- `getOp` returns a suffix of its input. -/
private theorem getOp_suffix (s r : BitcoinScript.Bytes) (i : Instr) (h : getOp s = some (i, r)) :
    ∃ pre, s = pre ++ r := by
  cases s with
  | nil => simp [getOp] at h
  | cons b rest =>
    simp only [getOp] at h
    split at h
    · split at h
      · simp at h
      · next sz r' hsz =>
          split at h
          · simp at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          -- r' is a suffix of rest
          have hr' : ∃ pre, rest = pre ++ r' := by
            split at hsz
            · simp at hsz; obtain ⟨_, rfl⟩ := hsz; exact ⟨[], rfl⟩
            · split at hsz
              · cases rest with
                | nil => simp at hsz
                | cons x xs => simp at hsz; obtain ⟨_, rfl⟩ := hsz; exact ⟨[x], rfl⟩
              · split at hsz
                · split at hsz
                  · simp at hsz
                  · simp at hsz; obtain ⟨_, rfl⟩ := hsz; exact ⟨rest.take 2, (List.take_append_drop 2 rest).symm⟩
                · split at hsz
                  · simp at hsz
                  · simp at hsz; obtain ⟨_, rfl⟩ := hsz; exact ⟨rest.take 4, (List.take_append_drop 4 rest).symm⟩
          obtain ⟨pre, rfl⟩ := hr'
          exact ⟨b :: pre ++ r'.take sz, by simp [List.take_append_drop]⟩
    · simp at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨[b], rfl⟩

/-- every annotated instruction is followed by a suffix of the script; a non-push opcode `c` is the byte
just before its suffix. -/
private theorem annotateAux_suffix : ∀ (n : Nat) (s : BitcoinScript.Bytes) (l : List (Instr × BitcoinScript.Bytes)),
    annotateAux n s = some l → ∀ i r, (i, r) ∈ l → (∃ pre, s = pre ++ r) ∧ (∀ c, i = .op c → ∃ pre, s = pre ++ c :: r)
  | _, [], l, h => by
    cases ‹Nat› <;> simp [annotateAux] at h <;> subst h <;> simp
  | 0, _ :: _, l, h => by simp [annotateAux] at h
  | n + 1, b :: s, l, h => by
    simp only [annotateAux] at h
    cases hg : getOp (b :: s) with
    | none => simp [hg] at h
    | some ir =>
      obtain ⟨i0, r0⟩ := ir
      simp only [hg] at h
      cases ha : annotateAux n r0 with
      | none => simp [ha] at h
      | some l0 =>
        simp only [ha, Option.some.injEq] at h
        subst h
        intro i r hm
        simp only [List.mem_cons, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | hm
        · constructor
          · exact getOp_suffix _ _ _ hg
          · intro c hc
            subst hc
            exact ⟨[], getOp_op _ _ _ hg⟩
        · have ih := annotateAux_suffix n r0 l0 ha i r hm
          obtain ⟨⟨pre, hpre⟩, hop⟩ := ih
          obtain ⟨pre0, hpre0⟩ := getOp_suffix _ _ _ hg
          constructor
          · exact ⟨pre0 ++ pre, by rw [hpre0, hpre, List.append_assoc]⟩
          · intro c hc
            obtain ⟨pre1, hpre1⟩ := hop c hc
            exact ⟨pre0 ++ pre1, by rw [hpre0, hpre1, List.append_assoc]⟩

private theorem multisigLoop_congr (o o' : Oracle) : ∀ (sigs keys : List Bytes),
    (∀ sig ∈ sigs, ∀ pk, o'.checkSig sig pk = o.checkSig sig pk) →
    multisigLoop o' sigs keys = multisigLoop o sigs keys
  | [], _, _ => by simp [multisigLoop]
  | _ :: _, [], _ => by simp [multisigLoop]
  | sig :: sigs, key :: keys, h => by
    simp only [multisigLoop]
    rw [h sig (by simp) key]
    cases o.checkSig sig key with
    | none => rfl
    | some ok =>
      simp only
      have ih1 := multisigLoop_congr o o' sigs keys (fun s hs pk => h s (by simp [hs]) pk)
      have ih2 := multisigLoop_congr o o' (sig :: sigs) keys h
      rw [ih1, ih2]

private theorem execOp_multisig_congr (f : Flags) (o : Oracle) (cs : Bytes → Bytes → Option Bool) (fExec : Bool)
    (c : Byte) (hc : c = OP_CHECKMULTISIG ∨ c = OP_CHECKMULTISIGVERIFY) (s : State)
    (h : ∀ sig ∈ multisigSigs s.stack, ∀ pk, cs sig pk = o.checkSig sig pk) :
    execOp f { o with checkSig := cs } fExec c s = execOp f o fExec c s := by
  rcases hc with rfl | rfl <;>
  · simp (config := {decide := true}) only [execOp, ↓reduceIte]
    cases hs : s.stack with
    | nil => simp
    | cons nk rest =>
      simp only [multisigSigs, hs] at h
      simp only []
      cases hk : toNum false nDefaultMaxNumSize nk with
      | none => rfl
      | some nKeys =>
        simp only [hk] at h ⊢
        split <;> rename_i h1 <;> (try simp only [h1, ↓reduceIte]) <;> (try rfl)
        split <;> rename_i h2 <;> (try simp only [h2, ↓reduceIte]) <;> (try rfl)
        split <;> rename_i h3 <;> (try simp only [h3, ↓reduceIte]) <;> (try rfl)
        cases hd : rest.drop nKeys.toNat with
        | nil => simp [hd]
        | cons ns rest' =>
          simp only [hd] at h ⊢
          cases hn : toNum false nDefaultMaxNumSize ns with
          | none => simp [hn]
          | some nSigs =>
            simp only [hn] at h ⊢
            split <;> rename_i h4 <;> (try simp only [h4, ↓reduceIte]) <;> (try rfl)
            split <;> rename_i h5 <;> (try simp only [h5, ↓reduceIte]) <;> (try rfl)
            rw [multisigLoop_congr o { o with checkSig := cs } _ _ h]

private theorem foldl_id {α β : Type} (g : α → β → α) : ∀ (l : List β) (a : α), (∀ x ∈ l, g a x = a) → l.foldl g a = a
  | [], _, _ => rfl
  | x :: l, a, h => by
    simp only [List.foldl_cons, h x (by simp)]
    exact foldl_id g l a (fun y hy => h y (by simp [hy]))

/-- `step` on a skipped (non-conditional) opcode does not consult the oracle. -/
private theorem step_skipped (f : Flags) (o o' : Oracle) (s : State) (c : Byte)
    (hex : allTrue s.vfExec = false) (hc : (OP_IF ≤ c && c ≤ OP_ENDIF) = false) :
    step f o' s (.op c) = step f o s (.op c) := by
  simp only [step, hex, hc, Bool.false_or, Bool.false_eq_true, if_false]

private theorem step_multisig_congr (f : Flags) (o : Oracle) (cs : Bytes → Bytes → Option Bool) (s : State)
    (c : Byte) (hc : c = OP_CHECKMULTISIG ∨ c = OP_CHECKMULTISIGVERIFY)
    (h : ∀ sig ∈ multisigSigs s.stack, ∀ pk, cs sig pk = o.checkSig sig pk) :
    step f { o with checkSig := cs } s (.op c) = step f o s (.op c) := by
  cases hex : allTrue s.vfExec with
  | false => exact step_skipped f o _ s c hex (by rcases hc with rfl | rfl <;> decide)
  | true =>
    rcases hc with rfl | rfl <;>
    · simp (config := {decide := true}) only [step, hex, Bool.true_or, if_true, Bool.true_and, isDisabled,
        ↓reduceIte, Bool.false_or]
      split
      · rfl
      · rw [execOp_multisig_congr f o cs true _ (by first | exact Or.inl rfl | exact Or.inr rfl)
          { s with opCount := s.opCount + 1 } h]

private theorem runV2_agree (f : Flags) (v : SigVersion) (o : OracleV2) :
    ∀ (l : List (Instr × Bytes)) (s : StateV2) (sc : Bytes), s.scriptCode = sc → RunOk f v o s l →
      runV2 f v o s l = (run f (withCodeSig o v sc) s.st (l.map Prod.fst)).map fun st => ⟨st, sc⟩
  | [], ⟨st, sc'⟩, sc, hsc, _ => by
    simp only at hsc; subst hsc
    simp only [runV2, run, List.map_nil]
    split <;> rfl
  | (i, r) :: rest, s, sc, hsc, hok => by
    obtain ⟨hstep, hrest⟩ := hok
    simp only [runV2, run, List.map_cons]
    rw [stepV2_agree f v o s sc hsc i r hstep]
    cases hst : step f (withCodeSig o v sc) s.st i with
    | none => rfl
    | some st =>
      simp only [Option.map_some]
      exact runV2_agree f v o rest ⟨st, sc⟩ sc rfl (hrest ⟨st, sc⟩ (by rw [stepV2_agree f v o s sc hsc i r hstep, hst]; rfl))

private theorem parseScript_p2pkh (h : Bytes) (hh : h.length = 20) :
    parseScript (p2pkhBytes h) = some (p2pkhScript h) := by
  have hp : pushBytes h = (0x14 : Byte) :: h := by
    simp only [pushBytes, hh]; rfl
  simp only [parseScript, p2pkhBytes, hp, List.cons_append, List.nil_append]
  simp (config := {decide := true}) [parseScriptAux, getOp, OP_PUSHDATA4, hh, p2pkhScript]

private theorem verifyWitnessProgram_agree (tap : TaprootHandler) (c : Ctx) (witness : List Bytes) (version : Nat)
    (program : Bytes) (isP2sh : Bool)
    (h4 : ∀ script, witness.getLast? = some script → EvalOk c .witnessV0 witness.dropLast.reverse script) :
    verifyWitnessProgramV2 tap c witness version program isP2sh = verifyWitnessProgram tap c witness version program isP2sh := by
  simp only [verifyWitnessProgramV2, verifyWitnessProgram]
  split
  · split
    · cases hw : witness.getLast? with
      | none => rfl
      | some script =>
        simp only
        split
        · rfl
        · simp only [executeWitnessScriptV0V2, executeWitnessScriptV0, evalBytes_agree c .witnessV0 _ _ (h4 script hw)]
          rfl
    · split
      · split
        · rfl
        · rename_i hlen hw2
          have hok : EvalOk c .witnessV0 witness.reverse (p2wpkhExec program) := by
            apply evalOk_witness
            intro s hs
            rw [p2wpkhExec, parseScript_p2pkh program (by simpa [WITNESS_V0_KEYHASH_SIZE] using hlen)] at hs
            simp only [Option.some.injEq] at hs
            subst hs
            simp (config := {decide := true}) [NoCodeSep, p2pkhScript]
          simp only [executeWitnessScriptV0V2, executeWitnessScriptV0, evalBytes_agree c .witnessV0 _ _ hok]
          rfl
      · rfl
  · rfl

/-- `VerifyScript` agrees with the published transcription whenever every script it executes (scriptSig,
scriptPubKey, redeem script, witness script) stays outside the two limits. -/
theorem solution (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (scriptSig scriptPubKey : BitcoinScript.Bytes) (witness : List BitcoinScript.Bytes)
    (h1 : BitcoinScriptV2.EvalOk c .base [] scriptSig)
    (h2 : ∀ st, BitcoinScriptV2.evalBytesV2 c .base [] scriptSig = some st → BitcoinScriptV2.EvalOk c .base st scriptPubKey)
    (h3 : ∀ redeem rest, BitcoinScriptV2.evalBytesV2 c .base [] scriptSig = some (redeem :: rest) →
      BitcoinScriptV2.EvalOk c .base rest redeem)
    (h4 : ∀ script, witness.getLast? = some script → BitcoinScriptV2.EvalOk c .witnessV0 witness.dropLast.reverse script) :
    BitcoinScriptV2.verifyScriptV2 tap c scriptSig scriptPubKey witness =
      BitcoinVerify.verifyScript tap c scriptSig scriptPubKey witness := by
  simp only [verifyScriptV2, verifyScript]
  have e1 := evalBytes_agree c .base [] scriptSig h1
  rw [e1]
  cases hS : evalBytes c .base [] scriptSig with
  | none => rfl
  | some stackSig =>
    have e2 := evalBytes_agree c .base stackSig scriptPubKey (h2 stackSig (by rw [e1, hS]))
    dsimp only
    rw [e2]
    cases evalBytes c .base stackSig scriptPubKey with
    | none => rfl
    | some stack =>
      dsimp only
      simp only [verifyWitnessProgram_agree tap c witness _ _ _ h4]
      cases stackSig with
      | nil => rfl
      | cons redeem rest =>
        have e3 := evalBytes_agree c .base rest redeem (h3 redeem rest (by rw [e1, hS]))
        simp only [e3]
        rfl
