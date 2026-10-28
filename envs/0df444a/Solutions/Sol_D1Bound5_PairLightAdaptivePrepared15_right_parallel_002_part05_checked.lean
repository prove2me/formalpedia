-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:46.061541+00:00
-- url     : https://prove2.me/submissions/2209af39-1ca4-438c-ab85-ae294747e26d

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 274 through 285, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 274) (PairLightPrepared15.rightRows.drop 274) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared15
end
