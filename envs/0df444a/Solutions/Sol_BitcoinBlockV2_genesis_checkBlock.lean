-- Prove2me | solution 1 for BitcoinBlockV2.genesis_checkBlock
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:12:13.569284+00:00
-- url     : https://prove2.me/submissions/9e0abb3c-3b8e-4d50-ad13-7203cb4c3641

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer
open BitcoinBlockV2 in
theorem solution : BitcoinBlockV2.checkBlock BitcoinSer.genesisBlock = true := by
  decide +kernel
