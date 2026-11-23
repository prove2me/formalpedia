-- Prove2me | solution 1 for DeletedPrimes.muS_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:46:05.082805+00:00
-- url     : https://prove2.me/submissions/4265f961-4a0a-4e95-9a20-ca317d2b78f2

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) : muS S 1 = 1 := by
  simp [muS]
end DeletedPrimes
