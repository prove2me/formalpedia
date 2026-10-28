-- Prove2me | solution 1 for BitcoinTaproot.merkleRoot_base
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:36:07.561997+00:00
-- url     : https://prove2.me/submissions/d7235015-b12c-4e19-8674-070346f3295c

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem solution (control leaf : Bytes) (h : control.length = BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE) :
    BitcoinTaproot.taprootMerkleRoot control leaf = leaf := by
  simp [taprootMerkleRoot, controlNodes, h, controlNodes.go]
