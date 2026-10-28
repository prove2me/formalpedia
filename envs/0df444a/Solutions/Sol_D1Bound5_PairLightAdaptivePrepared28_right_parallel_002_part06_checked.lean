-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.right_parallel_002_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:11:49.17488+00:00
-- url     : https://prove2.me/submissions/7c7a9b44-2f27-465c-9e68-99a45e6a6508

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

/-- Original heads 256 through 267, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 256) (PairLightPrepared28.rightRows.drop 256) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
