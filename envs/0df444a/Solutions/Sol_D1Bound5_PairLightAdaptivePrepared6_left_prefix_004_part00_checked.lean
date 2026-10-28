-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:46.445382+00:00
-- url     : https://prove2.me/submissions/c5759cf6-cded-4ecc-b664-3de05821e59a

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 318 through 337, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 20
      (PairLightPrepared6.leftCached.drop 318)
      (PairLightPrepared6.leftRows.drop 318) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
