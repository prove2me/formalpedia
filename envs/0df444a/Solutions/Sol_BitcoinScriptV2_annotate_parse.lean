-- Prove2me | solution 1 for BitcoinScriptV2.annotate_parse
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:28:34.486992+00:00
-- url     : https://prove2.me/submissions/b25e8a13-4324-4fb7-8774-6f6ab86dfb32

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

theorem solution (s : BitcoinScript.Bytes) :
    (BitcoinScriptV2.annotate s).map (List.map Prod.fst) = BitcoinSig.parseScript s := by
  exact annotateAux_parse s.length s
