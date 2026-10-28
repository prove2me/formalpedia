-- Prove2me | solution 1 for D1Bound5.PairLightPrepared5.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:15:03.127982+00:00
-- url     : https://prove2.me/submissions/9c9a31bf-fb11-4f69-891f-0e7cece5e5cb

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared5.left_signatures_checked





end D1Bound5.PairLightPrepared5
end
