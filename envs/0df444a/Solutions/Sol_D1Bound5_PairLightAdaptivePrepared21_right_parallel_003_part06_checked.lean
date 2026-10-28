-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.right_parallel_003_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:43:34.475801+00:00
-- url     : https://prove2.me/submissions/bcdb3ab6-e8bc-4b72-83e3-cd05a4d34b97

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 407 through 418, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 407) (PairLightPrepared21.rightRows.drop 407) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
