-- Prove2me | solution 1 for DeletedPrimes.resonance_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:17:20.378259+00:00
-- url     : https://prove2.me/submissions/b7029ff7-3bcc-4144-b3f9-225d6bc6d53e

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity

set_option autoImplicit false
open Real
open DeletedPrimes
open Classical
namespace DeletedPrimes
theorem _root_.solution {k d q m : ℤ} (hm : m = 1 ∨ m = -1) (h : k * q = m * d) : q ∣ d := by
  rcases hm with rfl | rfl
  · exact ⟨k, by linarith⟩
  · exact ⟨-k, by linarith⟩
end DeletedPrimes
