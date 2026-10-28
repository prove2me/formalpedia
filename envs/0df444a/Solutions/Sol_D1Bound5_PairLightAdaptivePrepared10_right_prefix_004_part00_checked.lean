-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.right_prefix_004_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:28:01.617531+00:00
-- url     : https://prove2.me/submissions/7f81379d-c866-4364-bf71-3b30635ccc6e

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

/-- Original heads 405 through 440, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 36
      (PairLightPrepared10.rightCached.drop 405)
      (PairLightPrepared10.rightRows.drop 405) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
