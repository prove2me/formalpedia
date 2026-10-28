-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:43:48.147321+00:00
-- url     : https://prove2.me/submissions/48e699f2-6b98-43c4-b75b-a53a6ba6d193

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 152 through 163, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 152) (PairLightPrepared15.rightRows.drop 152) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared15
end
