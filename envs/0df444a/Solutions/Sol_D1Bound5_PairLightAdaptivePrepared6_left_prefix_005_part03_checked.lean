-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_005_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:31:11.987012+00:00
-- url     : https://prove2.me/submissions/7dcfd0d3-2a8e-47c7-9182-2e50cd05238a

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 618 through 657, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 40
      (PairLightPrepared6.leftCached.drop 618)
      (PairLightPrepared6.leftRows.drop 618) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
