-- Prove2me | solution 1 for BitcoinUniqueness.scan_runs_early
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:57:47.16274+00:00
-- url     : https://prove2.me/submissions/d3005309-e3c1-4f9b-ac28-591752b260d5

import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader
open BitcoinUniqueness BitcoinSer BitcoinBlockV2
theorem solution (S : ChainState) (b : BitcoinSer.Block)
    (h : S.headers.length ≤ BitcoinHeader.BIP34Height)
    (hrep : BitcoinBlockV2.isBIP30Repeat S.nextHeight (BitcoinSer.headerHash b.header) = false) :
    BitcoinUniqueness.ScanRuns S b := by
  unfold BitcoinUniqueness.ScanRuns bip30Checked
  have hn : S.headers[BitcoinHeader.BIP34Height]? = none := List.getElem?_eq_none h
  simp [hn, hrep]
