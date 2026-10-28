-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_52_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:43:18.12955+00:00
-- url     : https://prove2.me/submissions/b7357a0b-b373-4186-a0b3-6a3afb31f651

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
import Definitions.Def_D1Bound5_OneSmallFourthData7_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002
import Theorems.Thm_D1Bound5_oneSmallDisk_300_1_6_eq
import Theorems.Thm_D1Bound5_oneSmallFourthGrowth_of_checked
import Theorems.Thm_D1Bound5_oneSmallFourth_52_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000


































theorem _root_.solution (z : QuadInt 1 6)
    (hz : z.norm < oneSmallTripleCutoff_52)
    (ha : ∃ q, q*q = oneSmallPairA_37*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_37*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_52*z+1) :
    z.norm ≤ 4*oneSmallPairB_37.norm*oneSmallTripleS_52.norm := by
  apply oneSmallFourthGrowth_of_checked (by decide)
    oneSmallPairA_37 oneSmallPairB_37 oneSmallTripleS_52
    (by decide) (by decide) oneSmallTripleCutoff_52 (by decide)
    oneSmallDisk_300_1_6 ?_ oneSmallFourth_52_checked z hz ha hb hs
  intro q hq; rw [oneSmallDisk_300_1_6_eq, List.mem_toFinset] at hq; exact hq






















end D1Bound5
end
