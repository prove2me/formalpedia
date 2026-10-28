-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_prefix_003_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:08:21.207736+00:00
-- url     : https://prove2.me/submissions/92a00a35-d353-4cfc-80c8-372f2a1f2006

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 255 through 274, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 20
      (PairLightPrepared4.rightCached.drop 255)
      (PairLightPrepared4.rightRows.drop 255) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
