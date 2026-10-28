-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:59.126141+00:00
-- url     : https://prove2.me/submissions/5f9c5131-9dfe-4dd0-97b4-591ee6492123

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 226 through 237, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 226) (PairLightPrepared30.rightRows.drop 226) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared30
end
