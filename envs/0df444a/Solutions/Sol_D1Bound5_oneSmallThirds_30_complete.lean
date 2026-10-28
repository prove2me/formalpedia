-- Prove2me | solution 1 for D1Bound5.oneSmallThirds_30_complete
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:46.133191+00:00
-- url     : https://prove2.me/submissions/102e9f10-2dc0-471f-bbf1-67f1af867206

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
import Theorems.Thm_D1Bound5_oneSmallDisk_224_1_2_eq
import Theorems.Thm_D1Bound5_oneSmallThirdCovered_of_checked
import Theorems.Thm_D1Bound5_oneSmallThirds_30_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000























































































































































































































































theorem _root_.solution (s : QuadInt 1 2) (hbound : s.norm ≤ 224)
    (horder : oneSmallPairB_30.norm ≤ s.norm)
    (ha : s ≠ oneSmallPairA_30) (hb : s ≠ oneSmallPairB_30)
    (hpair : PairExtension oneSmallPairA_30 oneSmallPairB_30 s) : s ∈ oneSmallThirds_30 := by
  apply oneSmallThirdCovered_of_checked (by decide) oneSmallPairA_30 oneSmallPairB_30
    oneSmallDisk_224_1_2 oneSmallThirds_30 ?_ oneSmallThirds_30_checked s hbound horder ha hb hpair
  intro q hq; rw [oneSmallDisk_224_1_2_eq, List.mem_toFinset] at hq; exact hq









































































end D1Bound5
end
