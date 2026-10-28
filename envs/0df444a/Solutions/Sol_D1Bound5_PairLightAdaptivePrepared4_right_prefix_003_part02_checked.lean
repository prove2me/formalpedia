-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_prefix_003_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:15.60249+00:00
-- url     : https://prove2.me/submissions/0fb158d6-2393-4582-9c5f-a5d47bf6519f

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

/-- Original heads 296 through 318, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 23
      (PairLightPrepared4.rightCached.drop 296)
      (PairLightPrepared4.rightRows.drop 296) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
