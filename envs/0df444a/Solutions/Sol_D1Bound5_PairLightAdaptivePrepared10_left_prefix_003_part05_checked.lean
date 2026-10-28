-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_003_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:29:28.223783+00:00
-- url     : https://prove2.me/submissions/1b34042e-2c21-4d38-abf8-d6c2244f58c0

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 371 through 401, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 31
      (PairLightPrepared10.leftCached.drop 371)
      (PairLightPrepared10.leftRows.drop 371) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
