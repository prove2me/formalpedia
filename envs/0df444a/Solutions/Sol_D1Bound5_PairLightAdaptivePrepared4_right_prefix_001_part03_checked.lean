-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_prefix_001_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:13.269254+00:00
-- url     : https://prove2.me/submissions/0c085e3e-671b-41e3-8581-54bfe33a3d0b

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

/-- Original heads 111 through 124, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 14
      (PairLightPrepared4.rightCached.drop 111)
      (PairLightPrepared4.rightRows.drop 111) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
