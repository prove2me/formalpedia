-- Prove2me | solution 1 for DeletedPrimes.log_two_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:08:18.780798+00:00
-- url     : https://prove2.me/submissions/b3676efa-2862-4056-acbb-44b5354a9034

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {p : ℕ} (hp : p ≠ 0) :
    2 ^ Nat.log 2 p ≤ p ∧ p < 2 * 2 ^ Nat.log 2 p := by
  refine ⟨Nat.pow_log_le_self 2 hp, ?_⟩
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
  rwa [pow_succ'] at this
end DeletedPrimes
