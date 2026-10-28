-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_002_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:00.951575+00:00
-- url     : https://prove2.me/submissions/53f17d8d-01f1-4fc3-9942-32a6e0d4e6f7

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

/-- Original heads 132 through 143, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 12
      (PairLightPrepared8.leftCached.drop 132)
      (PairLightPrepared8.leftRows.drop 132) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
