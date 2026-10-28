-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.left_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:38:10.674925+00:00
-- url     : https://prove2.me/submissions/f27b5429-d754-4af4-a8e4-2d998e5886bd

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 153 through 176, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.leftCached.drop 153)
      (PairLightPrepared5.leftRows.drop 153) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared5
end
