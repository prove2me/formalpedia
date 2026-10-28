-- Prove2me | solution 1 for D1Bound5.smallPairMask_0_6_1_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:50:17.703636+00:00
-- url     : https://prove2.me/submissions/11e3d247-eea8-4067-9ac1-44a84bfc3b2f

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





theorem _root_.solution : CoordinateSquareMaskValid 0 6 2 smallPairMask_0_6_1 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel










































































end D1Bound5
end
