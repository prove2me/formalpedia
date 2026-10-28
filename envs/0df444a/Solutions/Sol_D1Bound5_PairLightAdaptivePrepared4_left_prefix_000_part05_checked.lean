-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.left_prefix_000_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:57:28.963311+00:00
-- url     : https://prove2.me/submissions/7c4be9c9-5f91-4d80-b563-3fffb367c35d

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

/-- Original heads 58 through 70, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 13
      (PairLightPrepared4.leftCached.drop 58)
      (PairLightPrepared4.leftRows.drop 58) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
