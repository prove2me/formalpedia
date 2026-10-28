-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:31:45.698784+00:00
-- url     : https://prove2.me/submissions/26fa1b67-4b92-4d53-b52a-f132fb8e3a33

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

/-- Original heads 371 through 382, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 371) (PairLightPrepared28.rightRows.drop 371) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
