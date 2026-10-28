-- Prove2me | solution 1 for BitcoinVerify.witness_unexpected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:42:20.134252+00:00
-- url     : https://prove2.me/submissions/fb2596ff-5de2-4d37-9fdc-6effcf862049

import Definitions.Def_BitcoinVerify
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte
theorem S189B_wu (tap : TaprootHandler) (c : Ctx) (scriptSig spk : Bytes) (w : List Bytes)
    (hf : c.flags.witness = true) (hw : BitcoinVerify.isWitnessProgram spk = none)
    (hp : BitcoinVerify.isPayToScriptHash spk = false) (hne : w ≠ []) :
    BitcoinVerify.verifyScript tap c scriptSig spk w = false := by
  have hne' : w.isEmpty = false := by cases w <;> simp_all
  unfold verifyScript
  simp only [hf, hw, hp, hne', if_true, Bool.and_false, Bool.false_eq_true, if_false, Bool.not_false, Bool.and_self]
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem S189B_nm (tap : TaprootHandler) (c : Ctx) (scriptSig spk : Bytes)
    (w : List Bytes) (hf : c.flags.witness = true) (hw : BitcoinVerify.isWitnessProgram spk ≠ none)
    (hs : scriptSig ≠ []) : BitcoinVerify.verifyScript tap c scriptSig spk w = false := by
  obtain ⟨⟨v, p⟩, hvp⟩ := Option.ne_none_iff_exists'.1 hw
  unfold verifyScript
  simp only [hf, hvp, hs, if_true, ne_eq, not_false_eq_true]
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte
theorem solution (tap : TaprootHandler) (c : Ctx) (scriptSig spk : Bytes) (w : List Bytes)
    (hf : c.flags.witness = true) (hw : BitcoinVerify.isWitnessProgram spk = none)
    (hp : BitcoinVerify.isPayToScriptHash spk = false) (hne : w ≠ []) :
    BitcoinVerify.verifyScript tap c scriptSig spk w = false := by
  exact S189B_wu tap c scriptSig spk w hf hw hp hne
