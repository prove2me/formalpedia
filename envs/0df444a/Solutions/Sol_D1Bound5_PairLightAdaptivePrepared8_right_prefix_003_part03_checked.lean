-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_003_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:46:13.84507+00:00
-- url     : https://prove2.me/submissions/1871c2b8-518f-4019-b988-4388f716144c

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 232 through 245, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 14
      (PairLightPrepared8.rightCached.drop 232)
      (PairLightPrepared8.rightRows.drop 232) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
