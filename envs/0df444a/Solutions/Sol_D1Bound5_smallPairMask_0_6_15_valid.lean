-- Prove2me | solution 1 for D1Bound5.smallPairMask_0_6_15_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:49:19.380173+00:00
-- url     : https://prove2.me/submissions/afcdf62c-4d50-458a-b990-7ef4854eb639

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















































theorem _root_.solution : CoordinateSquareMaskValid 0 6 52 smallPairMask_0_6_15 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel
































end D1Bound5
end
