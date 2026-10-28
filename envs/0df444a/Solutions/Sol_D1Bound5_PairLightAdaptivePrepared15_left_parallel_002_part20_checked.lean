-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part20_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:20:14.556379+00:00
-- url     : https://prove2.me/submissions/1b04d283-3f86-4489-859c-510f1bebac0b

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 454 through 465, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 454) (PairLightPrepared15.leftRows.drop 454) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared15
end
