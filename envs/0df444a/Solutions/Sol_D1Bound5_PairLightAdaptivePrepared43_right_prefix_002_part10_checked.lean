-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.right_prefix_002_part10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:05:52.682982+00:00
-- url     : https://prove2.me/submissions/4ed51783-9ce0-4fe8-a86f-4d2e85bcc767

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 454 through 477, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 24
      (PairLightPrepared43.rightCached.drop 454)
      (PairLightPrepared43.rightRows.drop 454) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared43
end
