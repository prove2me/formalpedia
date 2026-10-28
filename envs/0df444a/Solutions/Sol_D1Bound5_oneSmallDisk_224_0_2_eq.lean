-- Prove2me | solution 1 for D1Bound5.oneSmallDisk_224_0_2_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:21.373998+00:00
-- url     : https://prove2.me/submissions/f79c62bf-5b65-43f0-9de1-9cca0fe0cd97

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











theorem _root_.solution : disk 0 2 224 = oneSmallDisk_224_0_2.toFinset := by
  have h : fastDiskList 0 2 224 = oneSmallDisk_224_0_2 := by decide +kernel
  rw [← fastDiskList_toFinset, h]





































































end D1Bound5
end
