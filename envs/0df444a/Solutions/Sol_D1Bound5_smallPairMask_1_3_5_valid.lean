-- Prove2me | solution 1 for D1Bound5.smallPairMask_1_3_5_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:52:06.407995+00:00
-- url     : https://prove2.me/submissions/4b3161cb-8b7c-41f3-88a6-d2c7aa3ecde0

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

















theorem _root_.solution : CoordinateSquareMaskValid 1 3 12 smallPairMask_1_3_5 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel






























































end D1Bound5
end
