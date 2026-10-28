-- Prove2me | solution 1 for D1Bound5.oneSmallThirds_20_complete
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:10.399712+00:00
-- url     : https://prove2.me/submissions/4ce6714a-5bda-4d93-a97a-1d924b415a80

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
import Theorems.Thm_D1Bound5_oneSmallThirds_20_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000







































































































































































theorem _root_.solution (s : QuadInt 1 1) (hbound : s.norm ≤ 224)
    (horder : oneSmallPairB_20.norm ≤ s.norm)
    (ha : s ≠ oneSmallPairA_20) (hb : s ≠ oneSmallPairB_20)
    (hpair : PairExtension oneSmallPairA_20 oneSmallPairB_20 s) : s ∈ oneSmallThirds_20 := by
  apply oneSmallThirdCovered_of_checked (by decide) oneSmallPairA_20 oneSmallPairB_20
    oneSmallDisk_224_1_1 oneSmallThirds_20 ?_ oneSmallThirds_20_checked s hbound horder ha hb hpair
  intro q hq; rw [oneSmallDisk_224_1_1_eq, List.mem_toFinset] at hq; exact hq

























































































































































end D1Bound5
end
