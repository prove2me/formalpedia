-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_45_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:43:24.867678+00:00
-- url     : https://prove2.me/submissions/c49e8652-2dac-40bc-9137-3cf324a90e3a

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
import Definitions.Def_D1Bound5_OneSmallFourthData6_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002
import Theorems.Thm_D1Bound5_oneSmallDisk_300_1_4_eq
import Theorems.Thm_D1Bound5_oneSmallFourthGrowth_of_checked
import Theorems.Thm_D1Bound5_oneSmallFourth_45_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000









































theorem _root_.solution (z : QuadInt 1 4)
    (hz : z.norm < oneSmallTripleCutoff_45)
    (ha : ∃ q, q*q = oneSmallPairA_33*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_33*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_45*z+1) :
    z.norm ≤ 4*oneSmallPairB_33.norm*oneSmallTripleS_45.norm := by
  apply oneSmallFourthGrowth_of_checked (by decide)
    oneSmallPairA_33 oneSmallPairB_33 oneSmallTripleS_45
    (by decide) (by decide) oneSmallTripleCutoff_45 (by decide)
    oneSmallDisk_300_1_4 ?_ oneSmallFourth_45_checked z hz ha hb hs
  intro q hq; rw [oneSmallDisk_300_1_4_eq, List.mem_toFinset] at hq; exact hq















end D1Bound5
end
