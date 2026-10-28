-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_40_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:27:22.89902+00:00
-- url     : https://prove2.me/submissions/82bb536b-db19-4a62-862f-2cdff8e36ecc

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
import Definitions.Def_D1Bound5_OneSmallFourthData6_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000




theorem _root_.solution :
    oneSmallFourthGrowthBool oneSmallPairA_29 oneSmallPairB_29 oneSmallTripleS_40
      oneSmallTripleCutoff_40 oneSmallDisk_300_1_2 = true := by
  decide +kernel




















































end D1Bound5
end
