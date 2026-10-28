-- Prove2me | solution 1 for D1Bound5.smallPairMask_1_6_3_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:56:13.368982+00:00
-- url     : https://prove2.me/submissions/ae03afdf-4ad8-4891-a1b5-c0aa896fc072

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











theorem _root_.solution : CoordinateSquareMaskValid 1 6 6 smallPairMask_1_6_3 := by
  apply coordinateSquareMaskCheck_sound
  decide +kernel




































































end D1Bound5
end
