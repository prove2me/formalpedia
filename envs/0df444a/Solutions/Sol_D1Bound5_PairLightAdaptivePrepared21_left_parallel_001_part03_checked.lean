-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.left_parallel_001_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:35:44.859519+00:00
-- url     : https://prove2.me/submissions/1537c3bf-4d71-494e-a855-4c0072b37b37

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

/-- Original heads 118 through 129, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 118) (PairLightPrepared21.leftRows.drop 118) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
