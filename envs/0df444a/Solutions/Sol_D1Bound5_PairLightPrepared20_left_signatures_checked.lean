-- Prove2me | solution 1 for D1Bound5.PairLightPrepared20.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:30:51.137982+00:00
-- url     : https://prove2.me/submissions/5553d926-651f-4af5-ac0b-3c4947fcf5c6

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared20_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared20.left_signatures_checked





end D1Bound5.PairLightPrepared20
end
