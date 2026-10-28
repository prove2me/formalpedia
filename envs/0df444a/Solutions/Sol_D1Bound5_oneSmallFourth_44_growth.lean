-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_44_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:42:09.423764+00:00
-- url     : https://prove2.me/submissions/a724acd8-b084-4c95-bba8-2c7a834bbdaa

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
import Theorems.Thm_D1Bound5_oneSmallDisk_300_1_3_eq
import Theorems.Thm_D1Bound5_oneSmallFourthGrowth_of_checked
import Theorems.Thm_D1Bound5_oneSmallFourth_44_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000


































theorem _root_.solution (z : QuadInt 1 3)
    (hz : z.norm < oneSmallTripleCutoff_44)
    (ha : ∃ q, q*q = oneSmallPairA_32*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_32*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_44*z+1) :
    z.norm ≤ 4*oneSmallPairB_32.norm*oneSmallTripleS_44.norm := by
  apply oneSmallFourthGrowth_of_checked (by decide)
    oneSmallPairA_32 oneSmallPairB_32 oneSmallTripleS_44
    (by decide) (by decide) oneSmallTripleCutoff_44 (by decide)
    oneSmallDisk_300_1_3 ?_ oneSmallFourth_44_checked z hz ha hb hs
  intro q hq; rw [oneSmallDisk_300_1_3_eq, List.mem_toFinset] at hq; exact hq






















end D1Bound5
end
