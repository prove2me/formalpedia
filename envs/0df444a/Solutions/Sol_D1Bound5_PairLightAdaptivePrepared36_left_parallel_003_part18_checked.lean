-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part18_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:18:05.925995+00:00
-- url     : https://prove2.me/submissions/6a3fa321-226d-4d53-95b0-28c24371902c

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 502 through 513, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 502) (PairLightPrepared36.leftRows.drop 502) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
