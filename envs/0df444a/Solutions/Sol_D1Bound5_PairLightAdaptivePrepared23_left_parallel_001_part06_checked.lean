-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared23.left_parallel_001_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:31:44.513117+00:00
-- url     : https://prove2.me/submissions/7f41feb3-69c0-4e58-875b-f8eeee4c7312

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 163 through 174, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 163) (PairLightPrepared23.leftRows.drop 163) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared23
end
