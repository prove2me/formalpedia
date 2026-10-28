-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared2.right_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:59:02.163898+00:00
-- url     : https://prove2.me/submissions/c05a4da3-21f3-4980-ae08-9723450f4c5f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData2_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 206; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared2.sieve 207
      rightCached000 rightRows000 = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared2
end
