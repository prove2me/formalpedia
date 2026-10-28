-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:31:35.011996+00:00
-- url     : https://prove2.me/submissions/27071fd8-d8b2-495e-81ad-f89009ee1cf7

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 211 through 211, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 1
      (PairLightPrepared30.leftCached.drop 211) (PairLightPrepared30.leftRows.drop 211) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared30
end
