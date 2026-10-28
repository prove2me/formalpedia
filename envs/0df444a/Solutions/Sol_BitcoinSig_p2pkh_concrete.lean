-- Prove2me | solution 1 for BitcoinSig.p2pkh_concrete
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:34:18.252993+00:00
-- url     : https://prove2.me/submissions/306d316a-5397-4c63-b241-d5caad5a444a

import Definitions.Def_BitcoinSig

namespace BS_e08b
open BitcoinSig BitcoinSer

abbrev BS_st (stk : List Bytes) (n : Nat) : BitcoinScript.State := ⟨stk, [], [], n⟩

theorem BS_dup (fl : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (pk sig : Bytes) :
    BitcoinScript.step fl o (BS_st [pk, sig] 0) (.op BitcoinScript.OP_DUP) = some (BS_st [pk, pk, sig] 1) := rfl

theorem BS_h160 (fl : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (pk sig : Bytes) :
    BitcoinScript.step fl o (BS_st [pk, pk, sig] 1) (.op BitcoinScript.OP_HASH160) =
      some (BS_st [o.hash160 pk, pk, sig] 2) := rfl

theorem BS_eqv (fl : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (H h pk sig : Bytes) :
    BitcoinScript.step fl o (BS_st [h, H, pk, sig] 2) (.op BitcoinScript.OP_EQUALVERIFY) =
      if decide (H = h) = true then some (BS_st [pk, sig] 3) else none := by
  by_cases e : H = h <;>
    simp [BitcoinScript.step, BitcoinScript.execOp, BitcoinScript.isDisabled, BitcoinScript.allTrue,
      BitcoinScript.MAX_STACK_SIZE, BitcoinScript.MAX_OPS_PER_SCRIPT, e, BitcoinScript.OP_1NEGATE, BitcoinScript.OP_1, BitcoinScript.OP_16, BitcoinScript.OP_NOP, BitcoinScript.OP_IF, BitcoinScript.OP_NOTIF, BitcoinScript.OP_ELSE, BitcoinScript.OP_ENDIF, BitcoinScript.OP_VERIFY, BitcoinScript.OP_RETURN, BitcoinScript.OP_TOALTSTACK, BitcoinScript.OP_FROMALTSTACK, BitcoinScript.OP_2DROP, BitcoinScript.OP_2DUP, BitcoinScript.OP_3DUP, BitcoinScript.OP_2OVER, BitcoinScript.OP_2ROT, BitcoinScript.OP_2SWAP, BitcoinScript.OP_IFDUP, BitcoinScript.OP_DEPTH, BitcoinScript.OP_DROP, BitcoinScript.OP_DUP, BitcoinScript.OP_NIP, BitcoinScript.OP_OVER, BitcoinScript.OP_PICK, BitcoinScript.OP_ROLL, BitcoinScript.OP_ROT, BitcoinScript.OP_SWAP, BitcoinScript.OP_TUCK, BitcoinScript.OP_CAT, BitcoinScript.OP_SUBSTR, BitcoinScript.OP_LEFT, BitcoinScript.OP_RIGHT, BitcoinScript.OP_SIZE, BitcoinScript.OP_INVERT, BitcoinScript.OP_AND, BitcoinScript.OP_OR, BitcoinScript.OP_XOR, BitcoinScript.OP_EQUAL, BitcoinScript.OP_EQUALVERIFY, BitcoinScript.OP_2MUL, BitcoinScript.OP_2DIV, BitcoinScript.OP_MUL, BitcoinScript.OP_DIV, BitcoinScript.OP_MOD, BitcoinScript.OP_LSHIFT, BitcoinScript.OP_RSHIFT, BitcoinScript.OP_NOP1, BitcoinScript.OP_CHECKLOCKTIMEVERIFY, BitcoinScript.OP_CHECKSEQUENCEVERIFY, BitcoinScript.OP_NOP4, BitcoinScript.OP_NOP10]

theorem BS_chk (fl : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (pk sig : Bytes) (r : Option Bool)
    (hr : o.checkSig sig pk = r) :
    BitcoinScript.step fl o (BS_st [pk, sig] 3) (.op BitcoinScript.OP_CHECKSIG) =
      r.map (fun ok => BS_st [BitcoinScript.boolBytes ok] 4) := by
  subst hr
  cases hc : o.checkSig sig pk <;>
    simp [BitcoinScript.step, BitcoinScript.execOp, BitcoinScript.isDisabled, BitcoinScript.allTrue,
      BitcoinScript.MAX_STACK_SIZE, BitcoinScript.MAX_OPS_PER_SCRIPT, hc, BitcoinScript.OP_1NEGATE, BitcoinScript.OP_1, BitcoinScript.OP_16, BitcoinScript.OP_NOP, BitcoinScript.OP_IF, BitcoinScript.OP_NOTIF, BitcoinScript.OP_ELSE, BitcoinScript.OP_ENDIF, BitcoinScript.OP_VERIFY, BitcoinScript.OP_RETURN, BitcoinScript.OP_TOALTSTACK, BitcoinScript.OP_FROMALTSTACK, BitcoinScript.OP_2DROP, BitcoinScript.OP_2DUP, BitcoinScript.OP_3DUP, BitcoinScript.OP_2OVER, BitcoinScript.OP_2ROT, BitcoinScript.OP_2SWAP, BitcoinScript.OP_IFDUP, BitcoinScript.OP_DEPTH, BitcoinScript.OP_DROP, BitcoinScript.OP_DUP, BitcoinScript.OP_NIP, BitcoinScript.OP_OVER, BitcoinScript.OP_PICK, BitcoinScript.OP_ROLL, BitcoinScript.OP_ROT, BitcoinScript.OP_SWAP, BitcoinScript.OP_TUCK, BitcoinScript.OP_CAT, BitcoinScript.OP_SUBSTR, BitcoinScript.OP_LEFT, BitcoinScript.OP_RIGHT, BitcoinScript.OP_SIZE, BitcoinScript.OP_INVERT, BitcoinScript.OP_AND, BitcoinScript.OP_OR, BitcoinScript.OP_XOR, BitcoinScript.OP_EQUAL, BitcoinScript.OP_EQUALVERIFY, BitcoinScript.OP_1ADD, BitcoinScript.OP_1SUB, BitcoinScript.OP_2MUL, BitcoinScript.OP_2DIV, BitcoinScript.OP_NEGATE, BitcoinScript.OP_ABS, BitcoinScript.OP_NOT, BitcoinScript.OP_0NOTEQUAL, BitcoinScript.OP_ADD, BitcoinScript.OP_SUB, BitcoinScript.OP_MUL, BitcoinScript.OP_DIV, BitcoinScript.OP_MOD, BitcoinScript.OP_LSHIFT, BitcoinScript.OP_RSHIFT, BitcoinScript.OP_BOOLAND, BitcoinScript.OP_BOOLOR, BitcoinScript.OP_NUMEQUAL, BitcoinScript.OP_NUMEQUALVERIFY, BitcoinScript.OP_NUMNOTEQUAL, BitcoinScript.OP_LESSTHAN, BitcoinScript.OP_GREATERTHAN, BitcoinScript.OP_LESSTHANOREQUAL, BitcoinScript.OP_GREATERTHANOREQUAL, BitcoinScript.OP_MIN, BitcoinScript.OP_MAX, BitcoinScript.OP_WITHIN, BitcoinScript.OP_RIPEMD160, BitcoinScript.OP_SHA1, BitcoinScript.OP_SHA256, BitcoinScript.OP_HASH160, BitcoinScript.OP_HASH256, BitcoinScript.OP_CODESEPARATOR, BitcoinScript.OP_CHECKSIG, BitcoinScript.OP_CHECKSIGVERIFY, BitcoinScript.OP_NOP1, BitcoinScript.OP_CHECKLOCKTIMEVERIFY, BitcoinScript.OP_CHECKSEQUENCEVERIFY, BitcoinScript.OP_NOP4, BitcoinScript.OP_NOP10]

theorem BS_push (fl : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (H h pk sig : Bytes)
    (hh : h.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.step fl o (BS_st [H, pk, sig] 2) (.push h) = some (BS_st [h, H, pk, sig] 2) := by
  have : ¬ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE < h.length := by omega
  simp [BitcoinScript.step, this, BitcoinScript.allTrue, BitcoinScript.MAX_STACK_SIZE]

theorem BS_sig (fl : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (sig pk : Bytes)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.evalScript fl o [] [.push sig, .push pk] = some [pk, sig] := by
  have h1 : ¬ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE < sig.length := by omega
  have h2 : ¬ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE < pk.length := by omega
  simp [BitcoinScript.evalScript, BitcoinScript.run, BitcoinScript.step, BitcoinScript.State.initial,
    BitcoinScript.allTrue, h1, h2, BitcoinScript.MAX_STACK_SIZE]

end BS_e08b

open BitcoinSig BitcoinSer in
theorem solution (f : SigFlags) (fl : BitcoinScript.Flags) (tx : Tx) (nIn : Nat) (amount : Int)
    (v : SigVersion) (sig pk h : Bytes)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hh : h.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.verifyScriptPlain fl (BitcoinSig.legacyOracle f tx nIn amount v (BitcoinSig.p2pkhBytes h))
        [.push sig, .push pk] (BitcoinScript.p2pkhScript h) = true ↔
      BitcoinSer.hash160 pk = h ∧
      BitcoinSig.checkSigPreTapscript f tx nIn amount v (BitcoinSig.p2pkhBytes h) sig pk = some true := by
  have hi : BitcoinScript.State.initial [pk, sig] = BS_e08b.BS_st [pk, sig] 0 := rfl
  have ho : (legacyOracle f tx nIn amount v (p2pkhBytes h)).hash160 = BitcoinSer.hash160 := rfl
  simp only [BitcoinScript.verifyScriptPlain, BS_e08b.BS_sig _ _ _ _ hsig hpk]
  simp only [BitcoinScript.evalScript,
    BitcoinScript.p2pkhScript, hi, BitcoinScript.run, BS_e08b.BS_dup, BS_e08b.BS_h160, ho,
    BS_e08b.BS_push _ _ _ _ _ _ hh, BS_e08b.BS_eqv]
  by_cases e : BitcoinSer.hash160 pk = h
  · simp only [e, decide_true, if_true]
    rw [BS_e08b.BS_chk _ _ _ _ _ rfl]
    have hc : (legacyOracle f tx nIn amount v (p2pkhBytes h)).checkSig sig pk =
        checkSigPreTapscript f tx nIn amount v (p2pkhBytes h) sig pk := rfl
    rw [hc]
    cases checkSigPreTapscript f tx nIn amount v (p2pkhBytes h) sig pk with
    | none => simp
    | some b => cases b <;> simp [BitcoinScript.boolBytes, BitcoinScript.vchTrue,
        BitcoinScript.vchFalse, BitcoinScript.castToBool]
  · simp [e]
