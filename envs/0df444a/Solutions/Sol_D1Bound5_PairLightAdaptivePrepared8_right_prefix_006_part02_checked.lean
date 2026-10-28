-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_006_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:38.818387+00:00
-- url     : https://prove2.me/submissions/9a51179d-8a2a-4b9e-b39b-287cea0b3cbf

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 604 through 664, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 61
      (PairLightPrepared8.rightCached.drop 604)
      (PairLightPrepared8.rightRows.drop 604) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
