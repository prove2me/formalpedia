-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.left_pilot12_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:42:20.136695+00:00
-- url     : https://prove2.me/submissions/d3a82824-006b-4361-b895-3fff282ddace

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 0 through 11, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 12
      (PairLightPrepared7.leftCached.drop 0)
      (PairLightPrepared7.leftRows.drop 0) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared7
end
