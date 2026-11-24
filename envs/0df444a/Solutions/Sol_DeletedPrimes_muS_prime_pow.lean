-- Prove2me | solution 1 for DeletedPrimes.muS_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:50:29.056438+00:00
-- url     : https://prove2.me/submissions/b2343bed-0013-4153-be5c-3396614c3df3

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) : muS S (p ^ k) = 0 := by
  unfold muS
  rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
  simp [show k ≠ 1 by omega]
end DeletedPrimes
