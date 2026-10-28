-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.left_prefix_000_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:42:11.948977+00:00
-- url     : https://prove2.me/submissions/d27342a0-168c-4c51-81df-c3149e3dbbf1

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 0 through 10, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 11
      (PairLightPrepared4.leftCached.drop 0)
      (PairLightPrepared4.leftRows.drop 0) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
