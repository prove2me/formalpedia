-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared24.left_prefix_000_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:54:52.565257+00:00
-- url     : https://prove2.me/submissions/257ba6f3-a93b-42e5-a33f-2172f75ee4d4

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 72 through 83, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 12
      (PairLightPrepared24.leftCached.drop 72)
      (PairLightPrepared24.leftRows.drop 72) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared24
end
