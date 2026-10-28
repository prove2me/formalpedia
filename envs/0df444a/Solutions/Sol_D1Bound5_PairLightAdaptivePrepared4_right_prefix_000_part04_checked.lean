-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:57:34.106005+00:00
-- url     : https://prove2.me/submissions/74dfbc26-bb1f-4feb-b4df-2f59cd05a2ed

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

/-- Original heads 46 through 57, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 12
      (PairLightPrepared4.rightCached.drop 46)
      (PairLightPrepared4.rightRows.drop 46) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
