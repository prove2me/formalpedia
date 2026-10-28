-- Prove2me | solution 1 for D1Bound5.smallPairMask_0_6_17_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:55:31.071283+00:00
-- url     : https://prove2.me/submissions/8d33fc5a-80b1-4dca-bca2-fbb370b2f882

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_CoordinateSquareMaskCheck_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_6_Definitions
import Theorems.Thm_D1Bound5_coordinateSquareMaskCheck_sound

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0





















































theorem _root_.solution : CoordinateSquareMaskValid 0 6 60 smallPairMask_0_6_17 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel


























end D1Bound5
end
