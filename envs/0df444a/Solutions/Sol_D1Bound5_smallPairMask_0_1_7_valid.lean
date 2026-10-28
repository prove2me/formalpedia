-- Prove2me | solution 1 for D1Bound5.smallPairMask_0_1_7_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:55:36.765781+00:00
-- url     : https://prove2.me/submissions/c582a5c4-d3fd-4a64-a781-5876b83fdcb2

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_CoordinateSquareMaskCheck_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_1_Definitions
import Theorems.Thm_D1Bound5_coordinateSquareMaskCheck_sound

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0























theorem _root_.solution : CoordinateSquareMaskValid 0 1 18 smallPairMask_0_1_7 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel
























































end D1Bound5
end
