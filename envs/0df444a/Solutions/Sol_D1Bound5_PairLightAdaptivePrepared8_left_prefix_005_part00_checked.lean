-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:07:59.561249+00:00
-- url     : https://prove2.me/submissions/bad1c289-06b5-4f97-bb2e-db6ad5b38633

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 376 through 395, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 20
      (PairLightPrepared8.leftCached.drop 376)
      (PairLightPrepared8.leftRows.drop 376) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
