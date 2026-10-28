-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.left_parallel_001_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:42:29.699793+00:00
-- url     : https://prove2.me/submissions/65b8c870-a87b-43b1-a78c-3df921c2ba78

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 139 through 150, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 139) (PairLightPrepared30.leftRows.drop 139) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared30
end
