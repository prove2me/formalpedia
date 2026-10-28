-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.right_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:27:53.723234+00:00
-- url     : https://prove2.me/submissions/08c77d80-aada-4c6d-b0ef-8dfdb7d4633b

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

/-- Original heads 11 through 21, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 11
      (PairLightPrepared10.rightCached.drop 11)
      (PairLightPrepared10.rightRows.drop 11) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
