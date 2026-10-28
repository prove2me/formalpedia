-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_prefix_003_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:23.332368+00:00
-- url     : https://prove2.me/submissions/fbe5c2c6-5473-4fc0-a95e-1e949bf9351b

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

/-- Original heads 275 through 295, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 21
      (PairLightPrepared4.rightCached.drop 275)
      (PairLightPrepared4.rightRows.drop 275) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
