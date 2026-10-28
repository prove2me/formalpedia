-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:52:51.88163+00:00
-- url     : https://prove2.me/submissions/2c7f30e6-ef36-403e-aa1b-694c2f8d0cae

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

/-- Original heads 22 through 33, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 12
      (PairLightPrepared4.rightCached.drop 22)
      (PairLightPrepared4.rightRows.drop 22) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
