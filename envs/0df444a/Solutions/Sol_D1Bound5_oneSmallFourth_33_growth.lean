-- Prove2me | solution 1 for D1Bound5.oneSmallFourth_33_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:22.188784+00:00
-- url     : https://prove2.me/submissions/16738a8a-b177-4ede-bb18-ae95423a3bd5

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
import Theorems.Thm_D1Bound5_oneSmallDisk_300_1_1_eq
import Theorems.Thm_D1Bound5_oneSmallFourthGrowth_of_checked
import Theorems.Thm_D1Bound5_oneSmallFourth_33_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000













theorem _root_.solution (z : QuadInt 1 1)
    (hz : z.norm < oneSmallTripleCutoff_33)
    (ha : ∃ q, q*q = oneSmallPairA_24*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_24*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_33*z+1) :
    z.norm ≤ 4*oneSmallPairB_24.norm*oneSmallTripleS_33.norm := by
  apply oneSmallFourthGrowth_of_checked (by decide)
    oneSmallPairA_24 oneSmallPairB_24 oneSmallTripleS_33
    (by decide) (by decide) oneSmallTripleCutoff_33 (by decide)
    oneSmallDisk_300_1_1 ?_ oneSmallFourth_33_checked z hz ha hb hs
  intro q hq; rw [oneSmallDisk_300_1_1_eq, List.mem_toFinset] at hq; exact hq











































end D1Bound5
end
