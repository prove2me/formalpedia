-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_001_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:42:15.409902+00:00
-- url     : https://prove2.me/submissions/bcfdafb2-89ab-4a9e-92dd-a9d3243af2c0

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

/-- Original heads 88 through 98, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 11
      (PairLightPrepared8.leftCached.drop 88)
      (PairLightPrepared8.leftRows.drop 88) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
