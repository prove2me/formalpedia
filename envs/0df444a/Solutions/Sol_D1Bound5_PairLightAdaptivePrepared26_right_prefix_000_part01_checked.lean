-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:41:04.451475+00:00
-- url     : https://prove2.me/submissions/5c9cb5e6-52ab-4dca-af53-6363b43c615d

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 3 through 5 of the original first block; every full tail is retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached000.drop 3) (rightRows000.drop 3) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
