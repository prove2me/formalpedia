-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_16_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:26:24.582988+00:00
-- url     : https://prove2.me/submissions/da2c8b55-819d-4121-bb59-08f123940209

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
import Definitions.Def_D1Bound5_OneSmallFourthData3_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000




theorem _root_.solution :
    oneSmallFourthGrowthBool oneSmallPairA_11 oneSmallPairB_11 oneSmallTripleS_16
      oneSmallTripleCutoff_16 oneSmallDisk_300_1_1 = true := by
  decide +kernel




















































end D1Bound5
end
