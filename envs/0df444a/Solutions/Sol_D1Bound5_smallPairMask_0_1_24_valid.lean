-- Prove2me | solution 1 for D1Bound5.smallPairMask_0_1_24_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:49:03.584533+00:00
-- url     : https://prove2.me/submissions/a09f5bbf-4533-4b2b-8966-63767ec5fd1d

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










































































theorem _root_.solution : CoordinateSquareMaskValid 0 1 96 smallPairMask_0_1_24 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel





end D1Bound5
end
