-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.left_prefix_004_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:35:48.236594+00:00
-- url     : https://prove2.me/submissions/6a8403ae-5314-4615-83b6-5e12ecf95167

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

/-- Original heads 550 through 595, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 46
      (PairLightPrepared4.leftCached.drop 550)
      (PairLightPrepared4.leftRows.drop 550) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
