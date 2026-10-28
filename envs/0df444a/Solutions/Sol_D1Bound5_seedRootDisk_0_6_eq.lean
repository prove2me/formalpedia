-- Prove2me | solution 1 for D1Bound5.seedRootDisk_0_6_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:02.101822+00:00
-- url     : https://prove2.me/submissions/fdd320c8-50f4-42f0-831e-a0b42ab1a7e8

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
import Definitions.Def_D1Bound5_TwoSmallSeedDisks_Definitions
import Theorems.Thm_D1Bound5_QuadInt_fastDiskList_toFinset

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000





theorem _root_.solution : disk 0 6 132 = seedRootDisk_0_6.toFinset := by
  have h : fastDiskList 0 6 132 = seedRootDisk_0_6 := by decide +kernel
  rw [← fastDiskList_toFinset, h]
















end D1Bound5
end
