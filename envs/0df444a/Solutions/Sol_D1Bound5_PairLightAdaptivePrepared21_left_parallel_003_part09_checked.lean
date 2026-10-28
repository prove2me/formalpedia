-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.left_parallel_003_part09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:22.706337+00:00
-- url     : https://prove2.me/submissions/6d60bb0f-ea16-4205-a63f-a94399842cb1

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

/-- Original heads 443 through 454, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 443) (PairLightPrepared21.leftRows.drop 443) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
