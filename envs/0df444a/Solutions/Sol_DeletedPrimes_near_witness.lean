-- Prove2me | solution 1 for DeletedPrimes.near_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:17:48.355019+00:00
-- url     : https://prove2.me/submissions/d62e2ea1-8ba8-4852-8613-a5bef8435c54

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity

set_option autoImplicit false
open Real
open DeletedPrimes
open Classical
namespace DeletedPrimes
theorem _root_.solution {q k a : ℤ} (ha : ¬ q ∣ a) : k * q - a ≠ 0 ∧ q ∣ a + (k * q - a) := by
  refine ⟨?_, ?_⟩
  · intro h
    apply ha
    exact ⟨k, by linarith⟩
  · rw [show a + (k * q - a) = q * k by ring]
    exact dvd_mul_right q k
end DeletedPrimes
