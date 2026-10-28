-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:37.424452+00:00
-- url     : https://prove2.me/submissions/0fb468a0-5f9c-451f-8ba2-5e6052f06924

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 226 through 237; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached003.drop 48) (leftRows003.drop 48) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
