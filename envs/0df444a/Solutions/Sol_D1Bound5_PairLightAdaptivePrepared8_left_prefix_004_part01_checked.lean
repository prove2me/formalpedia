-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_004_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:06:05.944991+00:00
-- url     : https://prove2.me/submissions/80cc976e-3541-462d-8a70-fb2745f75cbb

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

/-- Original heads 289 through 304, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 16
      (PairLightPrepared8.leftCached.drop 289)
      (PairLightPrepared8.leftRows.drop 289) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
