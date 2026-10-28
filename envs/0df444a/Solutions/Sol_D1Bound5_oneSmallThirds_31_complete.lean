-- Prove2me | solution 1 for D1Bound5.oneSmallThirds_31_complete
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:45:43.01444+00:00
-- url     : https://prove2.me/submissions/db1df8bb-bdaf-47a1-a722-515bbb2e48a2

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
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Theorems.Thm_D1Bound5_oneSmallDisk_224_1_3_eq
import Theorems.Thm_D1Bound5_oneSmallThirdCovered_of_checked
import Theorems.Thm_D1Bound5_oneSmallThirds_31_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000































































































































































































































































theorem _root_.solution (s : QuadInt 1 3) (hbound : s.norm ≤ 224)
    (horder : oneSmallPairB_31.norm ≤ s.norm)
    (ha : s ≠ oneSmallPairA_31) (hb : s ≠ oneSmallPairB_31)
    (hpair : PairExtension oneSmallPairA_31 oneSmallPairB_31 s) : s ∈ oneSmallThirds_31 := by
  apply oneSmallThirdCovered_of_checked (by decide) oneSmallPairA_31 oneSmallPairB_31
    oneSmallDisk_224_1_3 oneSmallThirds_31 ?_ oneSmallThirds_31_checked s hbound horder ha hb hpair
  intro q hq; rw [oneSmallDisk_224_1_3_eq, List.mem_toFinset] at hq; exact hq

































































end D1Bound5
end
