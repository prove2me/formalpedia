-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreeOneArbitraryPortsArithmetic
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:46:09.278232+00:00
-- url     : https://prove2.me/submissions/d713f78b-5c11-4834-bcfa-5d0c68c10b74

import Mathlib

namespace CubicP3Partition


end CubicP3Partition

open CubicP3Partition
theorem solution
    (b d : Nat) (hb : 1 ≤ b) (hd : 1 ≤ d) (hdn : d < 1 + 3 * b) :
    (d % 3 = 0 ∧ 3 ∣ d - 3 ∧ 3 ∣ (1 + 3 * b) - d - 1) ∨
    (d % 3 = 1 ∧ 3 ∣ d - 1 ∧ 3 ∣ (1 + 3 * b) - d - 3) ∨
    (d % 3 = 2 ∧ 3 ∣ d - 2 ∧ 3 ∣ (1 + 3 * b) - d - 2) := by
  have hmod : d % 3 < 3 := Nat.mod_lt _ (by omega)
  omega

