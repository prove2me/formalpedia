-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:35:23.738385+00:00
-- url     : https://prove2.me/submissions/0c70606a-2d22-42ab-9ccc-af7876ba3c7a

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 440 through 464, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 25
      (PairLightPrepared8.leftCached.drop 440)
      (PairLightPrepared8.leftRows.drop 440) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
