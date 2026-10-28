-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.left_parallel_002_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:43:53.896625+00:00
-- url     : https://prove2.me/submissions/4e258148-bd7d-4e6b-bd48-b465e8209b1a

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 196 through 207, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 196) (PairLightPrepared28.leftRows.drop 196) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
