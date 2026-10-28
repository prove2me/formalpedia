-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.left_parallel_001_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:08:23.306981+00:00
-- url     : https://prove2.me/submissions/d92858d9-a49c-4a59-81e7-4b1912887971

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 176 through 187, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 176) (PairLightPrepared15.leftRows.drop 176) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared15
end
