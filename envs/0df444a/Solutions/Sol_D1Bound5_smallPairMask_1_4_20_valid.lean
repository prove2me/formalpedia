-- Prove2me | solution 1 for D1Bound5.smallPairMask_1_4_20_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:57:23.214935+00:00
-- url     : https://prove2.me/submissions/0513b0f1-65c9-42bf-ae26-ef5e8e4584fb

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






























































theorem _root_.solution : CoordinateSquareMaskValid 1 4 72 smallPairMask_1_4_20 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel

















end D1Bound5
end
