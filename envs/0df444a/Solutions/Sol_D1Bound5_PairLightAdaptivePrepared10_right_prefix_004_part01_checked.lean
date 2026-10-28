-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.right_prefix_004_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:09.428977+00:00
-- url     : https://prove2.me/submissions/90fc2ce9-44de-4366-965e-2e7ea7fb45a3

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 441 through 485, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 45
      (PairLightPrepared10.rightCached.drop 441)
      (PairLightPrepared10.rightRows.drop 441) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
