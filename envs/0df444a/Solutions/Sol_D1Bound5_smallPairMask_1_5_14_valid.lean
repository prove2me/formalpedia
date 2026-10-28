-- Prove2me | solution 1 for D1Bound5.smallPairMask_1_5_14_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:57:30.043787+00:00
-- url     : https://prove2.me/submissions/bb346753-57df-41af-9666-90b25a737507

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












































theorem _root_.solution : CoordinateSquareMaskValid 1 5 46 smallPairMask_1_5_14 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel



































end D1Bound5
end
