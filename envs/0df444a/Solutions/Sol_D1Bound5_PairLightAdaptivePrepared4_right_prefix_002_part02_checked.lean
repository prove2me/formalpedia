-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_prefix_002_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:29.40045+00:00
-- url     : https://prove2.me/submissions/7a81e235-1af9-43cb-a4d1-9cdb1f495948

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

/-- Original heads 184 through 200, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 17
      (PairLightPrepared4.rightCached.drop 184)
      (PairLightPrepared4.rightRows.drop 184) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
