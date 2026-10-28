-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.left_prefix_003_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:14:10.456985+00:00
-- url     : https://prove2.me/submissions/5c4bcc06-81db-4010-bd77-b3b9a594159d

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

/-- Original heads 371 through 401, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 31
      (PairLightPrepared4.leftCached.drop 371)
      (PairLightPrepared4.leftRows.drop 371) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
