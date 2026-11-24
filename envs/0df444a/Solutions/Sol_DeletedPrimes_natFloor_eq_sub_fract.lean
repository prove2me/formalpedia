-- Prove2me | solution 1 for DeletedPrimes.natFloor_eq_sub_fract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:59:45.052797+00:00
-- url     : https://prove2.me/submissions/5fdd082c-0238-478f-96da-53432f442675

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution {u : ℝ} (hu : 0 ≤ u) : (⌊u⌋₊ : ℝ) = u - Int.fract u := by
  rw [Int.self_sub_fract, ← Int.natCast_floor_eq_floor hu, Int.cast_natCast]
end DeletedPrimes
