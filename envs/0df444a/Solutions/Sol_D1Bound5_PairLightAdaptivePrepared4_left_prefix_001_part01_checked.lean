-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.left_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:38:31.754969+00:00
-- url     : https://prove2.me/submissions/36908a16-c733-4c90-b721-68c698642022

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

/-- Original heads 84 through 96, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 13
      (PairLightPrepared4.leftCached.drop 84)
      (PairLightPrepared4.leftRows.drop 84) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
