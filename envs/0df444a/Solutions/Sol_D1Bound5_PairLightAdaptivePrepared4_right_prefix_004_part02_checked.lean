-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_prefix_004_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:59.474351+00:00
-- url     : https://prove2.me/submissions/27c0a59b-a1fd-4df6-9335-c1bb25852803

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

/-- Original heads 486 through 549, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 64
      (PairLightPrepared4.rightCached.drop 486)
      (PairLightPrepared4.rightRows.drop 486) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
