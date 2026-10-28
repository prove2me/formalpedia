-- Prove2me | solution 1 for D1Bound5.smallPairMask_1_5_23_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:55:56.144182+00:00
-- url     : https://prove2.me/submissions/4084f78d-88f8-44b7-a1fd-6c41677f4074

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







































































theorem _root_.solution : CoordinateSquareMaskValid 1 5 88 smallPairMask_1_5_23 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel








end D1Bound5
end
