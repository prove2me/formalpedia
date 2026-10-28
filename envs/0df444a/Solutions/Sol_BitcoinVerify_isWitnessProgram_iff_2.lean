-- Prove2me | solution 2 for BitcoinVerify.isWitnessProgram_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:56:55.207958+00:00
-- url     : https://prove2.me/submissions/fe6e0336-0957-44c9-956a-c5cc139e7ac3

import Definitions.Def_BitcoinVerify
import Theorems.Thm_BitcoinSig_parseScript_p2pkh
import Theorems.Thm_BitcoinScript_eval_pushes
import Theorems.Thm_BitcoinSer_sha256_length
import Theorems.Thm_BitcoinSer_hash160_length

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

/-- `IsWitnessProgram` holds exactly on `OP_n <2..40 bytes>` with `n ≤ 16`, yielding `n` and the bytes. -/
theorem solution (s : Bytes) (v : Nat) (prog : Bytes) :
    BitcoinVerify.isWitnessProgram s = some (v, prog) ↔
      v ≤ 16 ∧ 2 ≤ prog.length ∧ prog.length ≤ 40 ∧ s = BitcoinVerify.witnessBytes v prog := by
  constructor
  · intro hs
    unfold isWitnessProgram at hs
    match s, hs with
    | [], hs => simp at hs
    | [_], hs => simp at hs
    | a :: b :: rest, hs =>
      simp only [List.length_cons, List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons,
        List.drop_zero] at hs
      split at hs
      · cases hs
      · rename_i hlen
        (try dsimp only at hs)
        split at hs
        · cases hs
        · rename_i hb0
          split at hs
          · rename_i hl1
            simp only [Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨hv, rfl⟩ := hs
            have hb : b = BitVec.ofNat 8 rest.length := by
              have := ofNat_toNat' b; rw [show b.toNat = rest.length by omega] at this; exact this.symm
            refine ⟨?_, by omega, by omega, ?_⟩
            · rw [← hv]; unfold decodeOpN; have := a.isLt; split <;> omega
            · unfold witnessBytes
              rw [pushBytes_short _ (by omega), ← hb, ← hv]
              have ha := ofNat_toNat' a
              unfold decodeOpN
              by_cases h0 : a.toNat = 0
              · simp only [h0, ite_true]; rw [← ha, h0]
              · have e : (if (if a.toNat = 0 then 0 else a.toNat - 0x50) = 0 then 0
                    else 0x50 + if a.toNat = 0 then 0 else a.toNat - 0x50) = a.toNat := by
                  simp only [h0, ite_false]; rw [if_neg (by omega)]; omega
                rw [e, ha]
          · cases hs
  · rintro ⟨hv, h2, h40, rfl⟩
    unfold isWitnessProgram witnessBytes
    rw [pushBytes_short _ (by omega)]
    have hb0 : (BitVec.ofNat 8 (if v = 0 then 0 else 0x50 + v)).toNat = if v = 0 then 0 else 0x50 + v := by
      simp only [BitVec.toNat_ofNat, Nat.reducePow]; split <;> omega
    have hb1 : (BitVec.ofNat 8 prog.length).toNat = prog.length := by
      simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
    simp only [List.length_cons, List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons, List.drop_zero,
      hb0, hb1]
    rw [if_neg (by omega)]
    (try dsimp only)
    by_cases h0 : v = 0
    · subst h0; simp [decodeOpN]
    · simp only [h0, ite_false]
      rw [if_neg (by omega)]
      simp only [if_true, decodeOpN]
      rw [if_neg (by omega)]
      congr 2; omega
