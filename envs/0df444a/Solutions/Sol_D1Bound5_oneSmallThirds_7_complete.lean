-- Prove2me | solution 1 for D1Bound5.oneSmallThirds_7_complete
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:45:52.653988+00:00
-- url     : https://prove2.me/submissions/5fbc11ac-311d-4f12-82f6-4b0726642b80

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
import Theorems.Thm_D1Bound5_oneSmallThirds_7_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000































































theorem _root_.solution (s : QuadInt 0 2) (hbound : s.norm ≤ 224)
    (horder : oneSmallPairB_7.norm ≤ s.norm)
    (ha : s ≠ oneSmallPairA_7) (hb : s ≠ oneSmallPairB_7)
    (hpair : PairExtension oneSmallPairA_7 oneSmallPairB_7 s) : s ∈ oneSmallThirds_7 := by
  apply oneSmallThirdCovered_of_checked (by decide) oneSmallPairA_7 oneSmallPairB_7
    oneSmallDisk_224_0_2 oneSmallThirds_7 ?_ oneSmallThirds_7_checked s hbound horder ha hb hpair
  intro q hq; rw [oneSmallDisk_224_0_2_eq, List.mem_toFinset] at hq; exact hq

































































































































































































































































end D1Bound5
end
