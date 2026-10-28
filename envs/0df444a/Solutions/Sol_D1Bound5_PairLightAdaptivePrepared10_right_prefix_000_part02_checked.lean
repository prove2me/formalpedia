-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.right_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:50:58.468047+00:00
-- url     : https://prove2.me/submissions/6e6f88d5-ad30-4f30-835c-38ab46b91ae2

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

/-- Original heads 22 through 33, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 12
      (PairLightPrepared10.rightCached.drop 22)
      (PairLightPrepared10.rightRows.drop 22) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
