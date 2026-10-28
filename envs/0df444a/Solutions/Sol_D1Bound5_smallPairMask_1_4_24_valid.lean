-- Prove2me | solution 1 for D1Bound5.smallPairMask_1_4_24_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:50:40.87924+00:00
-- url     : https://prove2.me/submissions/23f24dea-9eea-4641-8f45-2320991cdbea

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_CoordinateSquareMaskCheck_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_4_Definitions
import Theorems.Thm_D1Bound5_coordinateSquareMaskCheck_sound

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0










































































theorem _root_.solution : CoordinateSquareMaskValid 1 4 96 smallPairMask_1_4_24 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel





end D1Bound5
end
