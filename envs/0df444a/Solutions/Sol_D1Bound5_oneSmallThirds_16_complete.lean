-- Prove2me | solution 1 for D1Bound5.oneSmallThirds_16_complete
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:14.698023+00:00
-- url     : https://prove2.me/submissions/1b7ea509-5562-47bd-8ea3-60e44ed5620c

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
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Theorems.Thm_D1Bound5_oneSmallDisk_224_1_1_eq
import Theorems.Thm_D1Bound5_oneSmallThirdCovered_of_checked
import Theorems.Thm_D1Bound5_oneSmallThirds_16_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000







































































































































theorem _root_.solution (s : QuadInt 1 1) (hbound : s.norm ≤ 224)
    (horder : oneSmallPairB_16.norm ≤ s.norm)
    (ha : s ≠ oneSmallPairA_16) (hb : s ≠ oneSmallPairB_16)
    (hpair : PairExtension oneSmallPairA_16 oneSmallPairB_16 s) : s ∈ oneSmallThirds_16 := by
  apply oneSmallThirdCovered_of_checked (by decide) oneSmallPairA_16 oneSmallPairB_16
    oneSmallDisk_224_1_1 oneSmallThirds_16 ?_ oneSmallThirds_16_checked s hbound horder ha hb hpair
  intro q hq; rw [oneSmallDisk_224_1_1_eq, List.mem_toFinset] at hq; exact hq

























































































































































































end D1Bound5
end
