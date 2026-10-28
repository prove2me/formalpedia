-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_prefix_002_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:27.930697+00:00
-- url     : https://prove2.me/submissions/e20a058c-0cbc-4d3c-a6de-fcf1ca175d25

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

/-- Original heads 201 through 217, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 17
      (PairLightPrepared4.rightCached.drop 201)
      (PairLightPrepared4.rightRows.drop 201) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
