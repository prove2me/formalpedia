-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_6_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:43:21.253886+00:00
-- url     : https://prove2.me/submissions/e4deae65-096a-41af-adf2-dc1d9389eaf2

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
import Definitions.Def_D1Bound5_OneSmallFourthData1_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001
import Theorems.Thm_D1Bound5_oneSmallDisk_300_0_1_eq
import Theorems.Thm_D1Bound5_oneSmallFourthGrowth_of_checked
import Theorems.Thm_D1Bound5_oneSmallFourth_6_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
















































theorem _root_.solution (z : QuadInt 0 1)
    (hz : z.norm < oneSmallTripleCutoff_6)
    (ha : ∃ q, q*q = oneSmallPairA_3*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_3*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_6*z+1) :
    z.norm ≤ 4*oneSmallPairB_3.norm*oneSmallTripleS_6.norm := by
  apply oneSmallFourthGrowth_of_checked (by decide)
    oneSmallPairA_3 oneSmallPairB_3 oneSmallTripleS_6
    (by decide) (by decide) oneSmallTripleCutoff_6 (by decide)
    oneSmallDisk_300_0_1 ?_ oneSmallFourth_6_checked z hz ha hb hs
  intro q hq; rw [oneSmallDisk_300_0_1_eq, List.mem_toFinset] at hq; exact hq








end D1Bound5
end
