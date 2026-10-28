-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_29_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:48:26.327822+00:00
-- url     : https://prove2.me/submissions/6310a587-1659-41e8-ba30-1c6ad5ec190e

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
import Definitions.Def_D1Bound5_OneSmallFourthData4_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002
import Theorems.Thm_D1Bound5_oneSmallDisk_300_1_1_eq
import Theorems.Thm_D1Bound5_oneSmallFourthGrowth_of_checked
import Theorems.Thm_D1Bound5_oneSmallFourth_29_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000









































theorem _root_.solution (z : QuadInt 1 1)
    (hz : z.norm < oneSmallTripleCutoff_29)
    (ha : ∃ q, q*q = oneSmallPairA_22*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_22*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_29*z+1) :
    z.norm ≤ 4*oneSmallPairB_22.norm*oneSmallTripleS_29.norm := by
  apply oneSmallFourthGrowth_of_checked (by decide)
    oneSmallPairA_22 oneSmallPairB_22 oneSmallTripleS_29
    (by decide) (by decide) oneSmallTripleCutoff_29 (by decide)
    oneSmallDisk_300_1_1 ?_ oneSmallFourth_29_checked z hz ha hb hs
  intro q hq; rw [oneSmallDisk_300_1_1_eq, List.mem_toFinset] at hq; exact hq















end D1Bound5
end
