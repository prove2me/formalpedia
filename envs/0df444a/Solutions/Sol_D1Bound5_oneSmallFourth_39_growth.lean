-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_39_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:42:06.279264+00:00
-- url     : https://prove2.me/submissions/cad300a1-d873-465b-bb3a-f3f37c60faf4

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
import Definitions.Def_D1Bound5_OneSmallFourthData5_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002
import Theorems.Thm_D1Bound5_oneSmallDisk_300_0_6_eq
import Theorems.Thm_D1Bound5_oneSmallFourthGrowth_of_checked
import Theorems.Thm_D1Bound5_oneSmallFourth_39_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000























































theorem _root_.solution (z : QuadInt 0 6)
    (hz : z.norm < oneSmallTripleCutoff_39)
    (ha : ∃ q, q*q = oneSmallPairA_28*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_28*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_39*z+1) :
    z.norm ≤ 4*oneSmallPairB_28.norm*oneSmallTripleS_39.norm := by
  apply oneSmallFourthGrowth_of_checked (by decide)
    oneSmallPairA_28 oneSmallPairB_28 oneSmallTripleS_39
    (by decide) (by decide) oneSmallTripleCutoff_39 (by decide)
    oneSmallDisk_300_0_6 ?_ oneSmallFourth_39_checked z hz ha hb hs
  intro q hq; rw [oneSmallDisk_300_0_6_eq, List.mem_toFinset] at hq; exact hq

end D1Bound5
end
