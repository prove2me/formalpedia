-- Prove2me | solution 1 for D1Bound5.smallPairMask_1_5_7_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:50:12.884388+00:00
-- url     : https://prove2.me/submissions/35e068f2-f3f7-4f3f-8af2-ee7925c13f2c

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_CoordinateSquareMaskCheck_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_5_Definitions
import Theorems.Thm_D1Bound5_coordinateSquareMaskCheck_sound

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0























theorem _root_.solution : CoordinateSquareMaskValid 1 5 18 smallPairMask_1_5_7 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel
























































end D1Bound5
end
