-- Prove2me | solution 1 for DeletedPrimes.abs_saw_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:59:59.663085+00:00
-- url     : https://prove2.me/submissions/fdae511e-adf0-4a59-80dc-1f6ddb82435b

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (u : ℝ) : |saw u| ≤ 1 / 2 := by
  unfold saw
  have h0 := Int.fract_nonneg u
  have h1 := Int.fract_lt_one u
  rw [abs_le]; constructor <;> linarith
end DeletedPrimes
