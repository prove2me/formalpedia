-- Prove2me | solution 1 for DeletedPrimes.muS_mul_of_not_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:14:34.130814+00:00
-- url     : https://prove2.me/submissions/000e5ca7-ec6b-488f-b043-fb1d991f66d4

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution {q d : ℕ} (h : ¬ Nat.Coprime q d) : muS S (q * d) = 0 := by
  unfold muS
  have : ArithmeticFunction.moebius (q * d) = 0 := by
    by_contra hne
    exact h (Nat.coprime_of_squarefree_mul (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hne))
  simp [this]
end DeletedPrimes
