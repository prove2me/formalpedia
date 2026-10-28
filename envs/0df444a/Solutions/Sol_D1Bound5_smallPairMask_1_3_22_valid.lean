-- Prove2me | solution 1 for D1Bound5.smallPairMask_1_3_22_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:51:01.146418+00:00
-- url     : https://prove2.me/submissions/7f4f7a72-b242-428b-9845-453b6eb3ec71

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_CoordinateSquareMaskCheck_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_3_Definitions
import Theorems.Thm_D1Bound5_coordinateSquareMaskCheck_sound

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0




































































theorem _root_.solution : CoordinateSquareMaskValid 1 3 82 smallPairMask_1_3_22 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel











end D1Bound5
end
