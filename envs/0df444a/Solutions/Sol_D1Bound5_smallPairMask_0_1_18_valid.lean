-- Prove2me | solution 1 for D1Bound5.smallPairMask_0_1_18_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:49:11.396165+00:00
-- url     : https://prove2.me/submissions/5045d56b-35da-43cd-8fcc-34365953373a

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
























































theorem _root_.solution : CoordinateSquareMaskValid 0 1 66 smallPairMask_0_1_18 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel























end D1Bound5
end
