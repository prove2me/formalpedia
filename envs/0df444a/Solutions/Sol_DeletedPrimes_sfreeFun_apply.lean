-- Prove2me | solution 1 for DeletedPrimes.sfreeFun_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:46:05.927808+00:00
-- url     : https://prove2.me/submissions/36ca40eb-f6e1-4a48-95f2-fa351f318e33

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (n : ℕ) : sfreeFun S n = if n ≠ 0 ∧ SFree S n then 1 else 0 := rfl
end DeletedPrimes
