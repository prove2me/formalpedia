-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:58:27.158926+00:00
-- url     : https://prove2.me/submissions/49fcf4ec-fdef-4b06-82c7-ab74a523a7d7

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

/-- Original heads 443 through 454, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 443) (PairLightPrepared28.rightRows.drop 443) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
