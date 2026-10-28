-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:57.821737+00:00
-- url     : https://prove2.me/submissions/d74ac866-481c-4942-8b01-a08cbdf2cc54

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

/-- Original heads 248 through 259, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 248) (PairLightPrepared23.leftRows.drop 248) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared23
end
