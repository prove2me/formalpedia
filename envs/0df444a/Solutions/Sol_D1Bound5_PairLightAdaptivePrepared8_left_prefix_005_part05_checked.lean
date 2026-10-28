-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:57:22.128562+00:00
-- url     : https://prove2.me/submissions/8128c3dd-ff52-47e3-becc-5a891ac2fc10

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

/-- Original heads 493 through 523, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 31
      (PairLightPrepared8.leftCached.drop 493)
      (PairLightPrepared8.leftRows.drop 493) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
