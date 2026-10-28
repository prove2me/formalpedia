-- Prove2me | solution 1 for D1Bound5.oneSmallThirds_25_complete
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:25.270398+00:00
-- url     : https://prove2.me/submissions/047087b0-cc85-4f66-bb5d-1636df5b8444

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
import Theorems.Thm_D1Bound5_oneSmallDisk_224_0_5_eq
import Theorems.Thm_D1Bound5_oneSmallThirdCovered_of_checked
import Theorems.Thm_D1Bound5_oneSmallThirds_25_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000















































































































































































































theorem _root_.solution (s : QuadInt 0 5) (hbound : s.norm ≤ 224)
    (horder : oneSmallPairB_25.norm ≤ s.norm)
    (ha : s ≠ oneSmallPairA_25) (hb : s ≠ oneSmallPairB_25)
    (hpair : PairExtension oneSmallPairA_25 oneSmallPairB_25 s) : s ∈ oneSmallThirds_25 := by
  apply oneSmallThirdCovered_of_checked (by decide) oneSmallPairA_25 oneSmallPairB_25
    oneSmallDisk_224_0_5 oneSmallThirds_25 ?_ oneSmallThirds_25_checked s hbound horder ha hb hpair
  intro q hq; rw [oneSmallDisk_224_0_5_eq, List.mem_toFinset] at hq; exact hq

















































































































end D1Bound5
end
