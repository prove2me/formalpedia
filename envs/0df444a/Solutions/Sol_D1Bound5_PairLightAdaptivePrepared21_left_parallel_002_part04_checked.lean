-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.left_parallel_002_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:32.054098+00:00
-- url     : https://prove2.me/submissions/465b46cf-ce4b-4679-9c70-480ded61c766

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 232 through 243, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 232) (PairLightPrepared21.leftRows.drop 232) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
