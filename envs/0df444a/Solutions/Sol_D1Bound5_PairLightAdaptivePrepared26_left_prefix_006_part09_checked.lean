-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_006_part09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:38:47.8018+00:00
-- url     : https://prove2.me/submissions/882518cb-6839-4ffa-808f-8b8768ab6c9a

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 551 through 562; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached006.drop 108) (leftRows006.drop 108) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
