-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:29:26.602544+00:00
-- url     : https://prove2.me/submissions/cfb8075e-bb99-48dc-b269-20416fb7365b

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

/-- Original heads 431 through 442, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 431) (PairLightPrepared28.rightRows.drop 431) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
