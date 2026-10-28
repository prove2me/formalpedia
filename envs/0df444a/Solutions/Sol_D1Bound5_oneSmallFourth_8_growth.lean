-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_8_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:43:03.686297+00:00
-- url     : https://prove2.me/submissions/4aec17b3-70e2-4ac8-8e6b-2f949b1e71f5

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
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_OneSmallDisks_Definitions
import Definitions.Def_D1Bound5_OneSmallFourthData2_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001
import Theorems.Thm_D1Bound5_oneSmallDisk_300_0_1_eq
import Theorems.Thm_D1Bound5_oneSmallFourthGrowth_of_checked
import Theorems.Thm_D1Bound5_oneSmallFourth_8_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000






theorem _root_.solution (z : QuadInt 0 1)
    (hz : z.norm < oneSmallTripleCutoff_8)
    (ha : ∃ q, q*q = oneSmallPairA_4*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_4*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_8*z+1) :
    z.norm ≤ 4*oneSmallPairB_4.norm*oneSmallTripleS_8.norm := by
  apply oneSmallFourthGrowth_of_checked (by decide)
    oneSmallPairA_4 oneSmallPairB_4 oneSmallTripleS_8
    (by decide) (by decide) oneSmallTripleCutoff_8 (by decide)
    oneSmallDisk_300_0_1 ?_ oneSmallFourth_8_checked z hz ha hb hs
  intro q hq; rw [oneSmallDisk_300_0_1_eq, List.mem_toFinset] at hq; exact hq


















































end D1Bound5
end
