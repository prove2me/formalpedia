-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:41:58.632788+00:00
-- url     : https://prove2.me/submissions/7bb332c9-7878-4ae4-9333-9dddd644b7fc

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

/-- Original heads 178 through 183, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 6
      (PairLightPrepared28.rightCached.drop 178) (PairLightPrepared28.rightRows.drop 178) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
