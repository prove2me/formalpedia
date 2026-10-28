-- Prove2me | solution 1 for D1Bound5.oneSmallDisk_300_0_5_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:23:56.558796+00:00
-- url     : https://prove2.me/submissions/a6f2827c-3d6d-42c5-8f70-6a6331477015

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























theorem _root_.solution : disk 0 5 300 = oneSmallDisk_300_0_5.toFinset := by
  have h : fastDiskList 0 5 300 = oneSmallDisk_300_0_5 := by decide +kernel
  rw [← fastDiskList_toFinset, h]

























































end D1Bound5
end
