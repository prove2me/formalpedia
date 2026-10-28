-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:54:59.004208+00:00
-- url     : https://prove2.me/submissions/b7231642-e2b0-44d5-9e98-15c7a1b14cf7

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 130 through 141, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 130) (PairLightPrepared28.rightRows.drop 130) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
