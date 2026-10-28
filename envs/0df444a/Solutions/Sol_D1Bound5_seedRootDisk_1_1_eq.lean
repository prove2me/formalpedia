-- Prove2me | solution 1 for D1Bound5.seedRootDisk_1_1_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:22.121176+00:00
-- url     : https://prove2.me/submissions/4099c5ff-0ad7-4cfc-af1b-4a89b74d08d6

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_FastDiskList_Definitions
import Definitions.Def_D1Bound5_PairSeedDisks_Definitions
import Theorems.Thm_D1Bound5_QuadInt_fastDiskList_toFinset

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000








theorem _root_.solution : disk 1 1 132 = seedRootDisk_1_1.toFinset := by
  have h : fastDiskList 1 1 132 = seedRootDisk_1_1 := by decide +kernel
  rw [← fastDiskList_toFinset, h]




end D1Bound5
end
