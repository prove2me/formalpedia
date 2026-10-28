-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_48_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:13:51.370639+00:00
-- url     : https://prove2.me/submissions/40ac1033-68e6-4344-8467-e7580aa309a1

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
import Definitions.Def_D1Bound5_OneSmallFourthData7_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000




theorem _root_.solution :
    oneSmallFourthGrowthBool oneSmallPairA_35 oneSmallPairB_35 oneSmallTripleS_48
      oneSmallTripleCutoff_48 oneSmallDisk_300_1_5 = true := by
  decide +kernel




















































end D1Bound5
end
