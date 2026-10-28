-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_004_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:50:34.362876+00:00
-- url     : https://prove2.me/submissions/5de149fe-8adf-4fcd-9ced-5e2323645d36

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

/-- Original heads 322 through 338, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 17
      (PairLightPrepared8.leftCached.drop 322)
      (PairLightPrepared8.leftRows.drop 322) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
