-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.left_prefix_003_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:46:07.371338+00:00
-- url     : https://prove2.me/submissions/5c34dd33-920f-4666-a194-5583b282a510

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

/-- Original heads 296 through 318, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 23
      (PairLightPrepared4.leftCached.drop 296)
      (PairLightPrepared4.leftRows.drop 296) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
