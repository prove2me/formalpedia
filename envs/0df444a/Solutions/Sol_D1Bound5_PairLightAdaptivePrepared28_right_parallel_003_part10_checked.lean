-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:24:30.941886+00:00
-- url     : https://prove2.me/submissions/f63c6d5a-7cb6-430e-836d-5043c3393cd0

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

/-- Original heads 455 through 466, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 455) (PairLightPrepared28.rightRows.drop 455) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
