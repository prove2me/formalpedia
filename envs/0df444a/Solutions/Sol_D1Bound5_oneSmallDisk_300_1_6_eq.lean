-- Prove2me | solution 1 for D1Bound5.oneSmallDisk_300_1_6_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:19.712315+00:00
-- url     : https://prove2.me/submissions/12a58af5-c57e-4d95-a7c3-78d1ad39fc3b

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
import Definitions.Def_D1Bound5_FastDiskList_Definitions
import Definitions.Def_D1Bound5_OneSmallDisks_Definitions
import Theorems.Thm_D1Bound5_QuadInt_fastDiskList_toFinset

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000















































































theorem _root_.solution : disk 1 6 300 = oneSmallDisk_300_1_6.toFinset := by
  have h : fastDiskList 1 6 300 = oneSmallDisk_300_1_6 := by decide +kernel
  rw [← fastDiskList_toFinset, h]

end D1Bound5
end
