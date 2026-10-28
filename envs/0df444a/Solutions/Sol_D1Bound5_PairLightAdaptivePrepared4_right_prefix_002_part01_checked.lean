-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_prefix_002_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:29.523737+00:00
-- url     : https://prove2.me/submissions/3ea3eae8-dac4-4705-b80e-faa1f0421e42

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

/-- Original heads 168 through 183, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 16
      (PairLightPrepared4.rightCached.drop 168)
      (PairLightPrepared4.rightRows.drop 168) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
