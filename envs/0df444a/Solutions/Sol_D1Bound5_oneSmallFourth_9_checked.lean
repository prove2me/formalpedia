-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_9_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:30:58.136021+00:00
-- url     : https://prove2.me/submissions/b41f95c1-0024-4f09-81d5-b06eefd7a2d6

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallDisks_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_OneSmallFourthData2_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000











theorem _root_.solution :
    oneSmallFourthGrowthBool oneSmallPairA_5 oneSmallPairB_5 oneSmallTripleS_9
      oneSmallTripleCutoff_9 oneSmallDisk_300_0_1 = true := by
  decide +kernel













































end D1Bound5
end
