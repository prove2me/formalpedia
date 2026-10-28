-- Prove2me | solution 1 for D1Bound5.oneSmallThirds_9_complete
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:46:02.248229+00:00
-- url     : https://prove2.me/submissions/2217c89a-8085-405a-be76-1048710c174e

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
import Theorems.Thm_D1Bound5_oneSmallDisk_224_0_2_eq
import Theorems.Thm_D1Bound5_oneSmallThirdCovered_of_checked
import Theorems.Thm_D1Bound5_oneSmallThirds_9_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000















































































theorem _root_.solution (s : QuadInt 0 2) (hbound : s.norm ≤ 224)
    (horder : oneSmallPairB_9.norm ≤ s.norm)
    (ha : s ≠ oneSmallPairA_9) (hb : s ≠ oneSmallPairB_9)
    (hpair : PairExtension oneSmallPairA_9 oneSmallPairB_9 s) : s ∈ oneSmallThirds_9 := by
  apply oneSmallThirdCovered_of_checked (by decide) oneSmallPairA_9 oneSmallPairB_9
    oneSmallDisk_224_0_2 oneSmallThirds_9 ?_ oneSmallThirds_9_checked s hbound horder ha hb hpair
  intro q hq; rw [oneSmallDisk_224_0_2_eq, List.mem_toFinset] at hq; exact hq

















































































































































































































































end D1Bound5
end
