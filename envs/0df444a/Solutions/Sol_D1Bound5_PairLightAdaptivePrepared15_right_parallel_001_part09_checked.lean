-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:06:31.55217+00:00
-- url     : https://prove2.me/submissions/5745e8dd-b6ee-4922-acf2-814cd328ca6a

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

/-- Original heads 200 through 211, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 200) (PairLightPrepared15.rightRows.drop 200) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared15
end
