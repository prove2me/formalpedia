-- Prove2me | solution 1 for D1Bound5.smallPairMask_1_2_2_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:50:30.752799+00:00
-- url     : https://prove2.me/submissions/05bb99d1-57a6-4805-a005-0fece304700e

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_CoordinateSquareMaskCheck_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_2_Definitions
import Theorems.Thm_D1Bound5_coordinateSquareMaskCheck_sound

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0








theorem _root_.solution : CoordinateSquareMaskValid 1 2 4 smallPairMask_1_2_2 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel







































































end D1Bound5
end
