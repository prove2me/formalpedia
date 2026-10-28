-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_004_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:18:21.635838+00:00
-- url     : https://prove2.me/submissions/a52a80c9-cb8c-488d-9550-b50db86b7eda

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

/-- Original heads 405 through 440, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 36
      (PairLightPrepared10.leftCached.drop 405)
      (PairLightPrepared10.leftRows.drop 405) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
