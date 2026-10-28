-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_41_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:43:31.577956+00:00
-- url     : https://prove2.me/submissions/51af7b7b-cfd8-4851-8973-3d7eed0c1e65

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
import Theorems.Thm_D1Bound5_oneSmallDisk_300_1_2_eq
import Theorems.Thm_D1Bound5_oneSmallFourthGrowth_of_checked
import Theorems.Thm_D1Bound5_oneSmallFourth_41_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000













theorem _root_.solution (z : QuadInt 1 2)
    (hz : z.norm < oneSmallTripleCutoff_41)
    (ha : ∃ q, q*q = oneSmallPairA_30*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_30*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_41*z+1) :
    z.norm ≤ 4*oneSmallPairB_30.norm*oneSmallTripleS_41.norm := by
  apply oneSmallFourthGrowth_of_checked (by decide)
    oneSmallPairA_30 oneSmallPairB_30 oneSmallTripleS_41
    (by decide) (by decide) oneSmallTripleCutoff_41 (by decide)
    oneSmallDisk_300_1_2 ?_ oneSmallFourth_41_checked z hz ha hb hs
  intro q hq; rw [oneSmallDisk_300_1_2_eq, List.mem_toFinset] at hq; exact hq











































end D1Bound5
end
