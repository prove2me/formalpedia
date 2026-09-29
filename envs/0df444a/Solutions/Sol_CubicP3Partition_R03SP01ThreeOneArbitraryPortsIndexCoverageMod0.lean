-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreeOneArbitraryPortsIndexCoverageMod0
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:21:41.719416+00:00
-- url     : https://prove2.me/submissions/d223a8c7-db48-4531-8728-8896f6d85c91

import Mathlib

namespace CubicP3Partition

open scoped Nat


end CubicP3Partition

open CubicP3Partition
open scoped Nat
theorem solution
    (b d : Nat) (hd : 1 ≤ d) (hdn : d < 1 + 3 * b) (hr : d % 3 = 0) :
    ({0, 1, d - 1, d} ∪ Finset.Icc 2 (d - 2) ∪
      Finset.Icc (d + 1) ((1 + 3 * b) - 1)) = Finset.range (1 + 3 * b) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_Icc, Finset.mem_range]
  have hmod : d % 3 < 3 := Nat.mod_lt _ (by omega)
  omega

