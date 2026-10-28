-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.right_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:15.277363+00:00
-- url     : https://prove2.me/submissions/9e69498f-1a68-4c46-942c-24676c4c62a3

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

/-- Original heads 46 through 57, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 12
      (PairLightPrepared10.rightCached.drop 46)
      (PairLightPrepared10.rightRows.drop 46) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
