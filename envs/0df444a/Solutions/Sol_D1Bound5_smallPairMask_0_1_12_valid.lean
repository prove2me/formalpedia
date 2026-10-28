-- Prove2me | solution 1 for D1Bound5.smallPairMask_0_1_12_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:52:30.639+00:00
-- url     : https://prove2.me/submissions/ac70c8eb-53a1-47a8-8d5f-b9b8d2595339

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






































theorem _root_.solution : CoordinateSquareMaskValid 0 1 40 smallPairMask_0_1_12 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel









































end D1Bound5
end
