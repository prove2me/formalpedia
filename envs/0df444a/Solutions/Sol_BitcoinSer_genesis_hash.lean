-- Prove2me | solution 1 for BitcoinSer.genesis_hash
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:04:04.897984+00:00
-- url     : https://prove2.me/submissions/eb18f7d4-5436-4b24-8421-505054721f13

import Definitions.Def_BitcoinSer
open BitcoinSer in
theorem solution : BitcoinSer.headerHash BitcoinSer.genesisHeader = BitcoinSer.genesisHash := by
  decide +kernel
