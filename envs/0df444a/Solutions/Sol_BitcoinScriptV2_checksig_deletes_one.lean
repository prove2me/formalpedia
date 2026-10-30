-- Prove2me | solution 1 for BitcoinScriptV2.checksig_deletes_one
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:28:37.737191+00:00
-- url     : https://prove2.me/submissions/b9785e18-eb17-4192-8b71-0f6356ee87f6

import Definitions.Def_BitcoinScriptV2

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

/-- The CHECKSIG oracle: `EvalChecksigPreTapscript` on the script code. -/
theorem solution (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s : BitcoinScriptV2.StateV2) (c : BitcoinScript.Byte)
    (hc : c = BitcoinScript.OP_CHECKSIG ∨ c = BitcoinScript.OP_CHECKSIGVERIFY) (sig pk : BitcoinScript.Bytes) :
    (BitcoinScriptV2.oracleAt v o s (.op c)).checkSig sig pk =
      o.checkSig (BitcoinScriptV2.fadSig v s.scriptCode sig) sig pk := by
  rcases hc with rfl | rfl <;> rfl
