-- Prove2me | solution 1 for BitDFT.ReaderHostFrame.tracked_input_word_embeds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T18:41:40.363553+00:00
-- url     : https://prove2.me/submissions/d9ebaf22-fd35-472e-a324-b164d3026e80

import Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open IntMul

theorem solution (A M H : MultitapeTM) (x y : List Bool) :
    ((IntMul.TrackedBankPreparation.inputWord M x y).map
        (fun s : M.Sym => some (s, true))).map
        (BitDFT.TripleAlphabet.multiplier A
          (BitDFT.ReaderHostFrame.tracked M) H).encode =
      x.map (BitDFT.ReaderHostFrame.host A M H).bitSym ++
        (BitDFT.ReaderHostFrame.host A M H).sep ::
          y.map (BitDFT.ReaderHostFrame.host A M H).bitSym := by
  let X := BitDFT.ReaderHostFrame.tracked M
  let N := BitDFT.ReaderHostFrame.host A M H
  let e := BitDFT.TripleAlphabet.multiplier A X H
  have hbit (b : Bool) : e.encode (some (M.bitSym b, true)) = N.bitSym b := by
    cases b
    · change e.encode X.zero = N.zero
      exact e.zero
    · change e.encode X.one = N.one
      exact e.one
  have hsep : e.encode (some (M.sep, true)) = N.sep := by
    change e.encode X.sep = N.sep
    exact e.sep
  have hsep' : (BitDFT.TripleAlphabet.multiplier A X H).encode
      (some (M.sep, true)) = N.sep := by
    simpa [e] using hsep
  have hbits (w : List Bool) :
      List.map (e.encode ∘ (fun s => some (s, true))) (w.map M.bitSym) =
        w.map N.bitSym := by
    induction w with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.map_cons]
      change e.encode (some (M.bitSym b, true)) ::
          List.map (e.encode ∘ (fun s => some (s, true))) (bs.map M.bitSym) = _
      rw [hbit b, ih]
      rfl
  simp only [IntMul.TrackedBankPreparation.inputWord, List.map_map]
  rw [List.map_append, List.map_cons]
  rw [hbits x, hbits y]
  simp only [Function.comp_apply]
  rw [hsep']
  rfl
end
