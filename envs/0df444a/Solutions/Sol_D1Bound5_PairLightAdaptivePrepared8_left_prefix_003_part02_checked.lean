-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_003_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:25:24.598291+00:00
-- url     : https://prove2.me/submissions/4e232789-5658-4c83-a210-5847ecb8d466

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

/-- Original heads 218 through 231, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 14
      (PairLightPrepared8.leftCached.drop 218)
      (PairLightPrepared8.leftRows.drop 218) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
