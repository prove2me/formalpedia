-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:54:38.557976+00:00
-- url     : https://prove2.me/submissions/81d9d5b4-f0bf-4976-8813-d3c97b3aef70

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 46 through 57, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 12
      (PairLightPrepared10.leftCached.drop 46)
      (PairLightPrepared10.leftRows.drop 46) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
