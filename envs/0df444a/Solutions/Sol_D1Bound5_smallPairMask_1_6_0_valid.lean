-- Prove2me | solution 1 for D1Bound5.smallPairMask_1_6_0_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:57:34.301634+00:00
-- url     : https://prove2.me/submissions/6ecaf012-6121-448f-8a58-68b5cf40e5b6

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_CoordinateSquareMaskCheck_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_6_Definitions
import Theorems.Thm_D1Bound5_coordinateSquareMaskCheck_sound

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.solution : CoordinateSquareMaskValid 1 6 1 smallPairMask_1_6_0 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel













































































end D1Bound5
end
