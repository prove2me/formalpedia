-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared38.left_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:54:50.738093+00:00
-- url     : https://prove2.me/submissions/82fb9c0d-f161-46ab-9273-afa694a2c73d

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 140 through 279; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 140
      (leftCached000.drop 140) (leftRows000.drop 140) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared38
end
