-- Prove2me | solution 1 for BitcoinTaproot.sighash_single_missing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:41:35.896748+00:00
-- url     : https://prove2.me/submissions/1682ed12-c728-4ab9-8a75-494b34fdc59c

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem solution (tx : Tx) (spent : List TxOut) (inPos hashType : Nat) (tapscript : Bool) (ed : ExecData)
    (hv : hashType ≤ 3 ∨ (0x81 ≤ hashType ∧ hashType ≤ 0x83)) (h3 : hashType &&& 3 = 3) (hout : tx.vout.length ≤ inPos) :
    BitcoinTaproot.sigHashSchnorr tx spent inPos hashType tapscript ed = none := by
  have h0 : hashType ≠ 0 := by intro h; subst h; simp at h3
  unfold sigHashSchnorr
  rw [if_neg (fun h => h hv)]
  simp [h0, h3, SIGHASH_DEFAULT, BitcoinSig.SIGHASH_SINGLE, hout]
