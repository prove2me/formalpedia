-- Prove2me | solution 1 for BitcoinUniqueness.scan_runs_late
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:57:46.036689+00:00
-- url     : https://prove2.me/submissions/0b4e6ede-7a7c-4517-9c2f-ff48576f4574

import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
open BitcoinUniqueness BitcoinSer BitcoinBlockV2
theorem solution (S : ChainState) (b : BitcoinSer.Block)
    (h : BIP34_IMPLIES_BIP30_LIMIT ≤ S.nextHeight) : BitcoinUniqueness.ScanRuns S b := by
  unfold BitcoinUniqueness.ScanRuns bip30Checked
  simp [h]
