-- Prove2me | solution 1 for BitcoinTaproot.sighash_type_invalid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:41:28.548248+00:00
-- url     : https://prove2.me/submissions/2a3c67b0-3875-40b2-8344-9de04e38f340

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem solution (tx : Tx) (spent : List TxOut) (inPos hashType : Nat) (tapscript : Bool) (ed : ExecData)
    (h : ¬ (hashType ≤ 3 ∨ (0x81 ≤ hashType ∧ hashType ≤ 0x83))) :
    BitcoinTaproot.sigHashSchnorr tx spent inPos hashType tapscript ed = none := by
  unfold sigHashSchnorr
  rw [if_pos h]
