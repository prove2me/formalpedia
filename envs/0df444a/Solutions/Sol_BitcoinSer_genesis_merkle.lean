-- Prove2me | solution 1 for BitcoinSer.genesis_merkle
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:04:01.590574+00:00
-- url     : https://prove2.me/submissions/1a639bfc-5ea8-47a8-aa9a-c0c2f13f892b

import Definitions.Def_BitcoinSer
open BitcoinSer in
theorem solution : BitcoinSer.txid BitcoinSer.genesisCoinbase = BitcoinSer.genesisMerkleRoot := by
  decide +kernel
