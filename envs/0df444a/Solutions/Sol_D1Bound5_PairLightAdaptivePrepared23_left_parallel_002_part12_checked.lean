-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part12_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:44:19.855486+00:00
-- url     : https://prove2.me/submissions/d9286c64-e415-480e-abd1-c60edd7b9b00

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

/-- Original heads 356 through 367, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 356) (PairLightPrepared23.leftRows.drop 356) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared23
end
