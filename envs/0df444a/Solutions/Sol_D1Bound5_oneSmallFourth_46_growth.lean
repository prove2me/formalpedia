-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_46_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:43:10.262139+00:00
-- url     : https://prove2.me/submissions/c0f85bcf-8edf-4173-b570-3dee9378e369

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
import Theorems.Thm_D1Bound5_oneSmallFourth_46_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
















































theorem _root_.solution (z : QuadInt 1 4)
    (hz : z.norm < oneSmallTripleCutoff_46)
    (ha : ∃ q, q*q = oneSmallPairA_33*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_33*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_46*z+1) :
    z.norm ≤ 4*oneSmallPairB_33.norm*oneSmallTripleS_46.norm := by
  apply oneSmallFourthGrowth_of_checked (by decide)
    oneSmallPairA_33 oneSmallPairB_33 oneSmallTripleS_46
    (by decide) (by decide) oneSmallTripleCutoff_46 (by decide)
    oneSmallDisk_300_1_4 ?_ oneSmallFourth_46_checked z hz ha hb hs
  intro q hq; rw [oneSmallDisk_300_1_4_eq, List.mem_toFinset] at hq; exact hq








end D1Bound5
end
