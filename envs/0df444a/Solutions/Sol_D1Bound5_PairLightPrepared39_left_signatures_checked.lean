-- Prove2me | solution 1 for D1Bound5.PairLightPrepared39.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:26:22.979884+00:00
-- url     : https://prove2.me/submissions/aaf4734f-afa5-4f05-bfe2-ea01517e0617

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared39.left_signatures_checked





end D1Bound5.PairLightPrepared39
end
