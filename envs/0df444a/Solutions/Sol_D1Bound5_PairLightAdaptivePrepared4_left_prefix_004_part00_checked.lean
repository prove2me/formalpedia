-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.left_prefix_004_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:25:46.100781+00:00
-- url     : https://prove2.me/submissions/37868a1c-fc2c-4c86-a75a-b8fb08a0d3fd

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

/-- Original heads 405 through 440, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 36
      (PairLightPrepared4.leftCached.drop 405)
      (PairLightPrepared4.leftRows.drop 405) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
