-- Prove2me | solution 1 for D1Bound5.oneSmallThirds_32_complete
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:45:53.616309+00:00
-- url     : https://prove2.me/submissions/87aad73a-3820-4053-84b0-d1aaeb5a6659

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
import Theorems.Thm_D1Bound5_oneSmallThirds_32_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000







































































































































































































































































theorem _root_.solution (s : QuadInt 1 3) (hbound : s.norm ≤ 224)
    (horder : oneSmallPairB_32.norm ≤ s.norm)
    (ha : s ≠ oneSmallPairA_32) (hb : s ≠ oneSmallPairB_32)
    (hpair : PairExtension oneSmallPairA_32 oneSmallPairB_32 s) : s ∈ oneSmallThirds_32 := by
  apply oneSmallThirdCovered_of_checked (by decide) oneSmallPairA_32 oneSmallPairB_32
    oneSmallDisk_224_1_3 oneSmallThirds_32 ?_ oneSmallThirds_32_checked s hbound horder ha hb hpair
  intro q hq; rw [oneSmallDisk_224_1_3_eq, List.mem_toFinset] at hq; exact hq

























































end D1Bound5
end
