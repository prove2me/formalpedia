-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_49_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:48:28.163981+00:00
-- url     : https://prove2.me/submissions/14379513-f3af-44c3-b167-f2e756b1a49f

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
import Theorems.Thm_D1Bound5_oneSmallDisk_300_1_5_eq
import Theorems.Thm_D1Bound5_oneSmallFourthGrowth_of_checked
import Theorems.Thm_D1Bound5_oneSmallFourth_49_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000













theorem _root_.solution (z : QuadInt 1 5)
    (hz : z.norm < oneSmallTripleCutoff_49)
    (ha : ∃ q, q*q = oneSmallPairA_35*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_35*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_49*z+1) :
    z.norm ≤ 4*oneSmallPairB_35.norm*oneSmallTripleS_49.norm := by
  apply oneSmallFourthGrowth_of_checked (by decide)
    oneSmallPairA_35 oneSmallPairB_35 oneSmallTripleS_49
    (by decide) (by decide) oneSmallTripleCutoff_49 (by decide)
    oneSmallDisk_300_1_5 ?_ oneSmallFourth_49_checked z hz ha hb hs
  intro q hq; rw [oneSmallDisk_300_1_5_eq, List.mem_toFinset] at hq; exact hq











































end D1Bound5
end
