-- Prove2me | solution 1 for DeletedPrimes.sFree_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:58:09.671225+00:00
-- url     : https://prove2.me/submissions/5074c8d5-3721-4f2d-aa27-ca28280bd4c2

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (hS : ∀ p ∈ S, p.Prime) {m n : ℕ} :
    SFree S (m * n) ↔ SFree S m ∧ SFree S n := by
  constructor
  · intro h
    exact ⟨fun p hp hdvd => h p hp (dvd_mul_of_dvd_left hdvd n),
      fun p hp hdvd => h p hp (dvd_mul_of_dvd_right hdvd m)⟩
  · rintro ⟨hm, hn⟩ p hp hdvd
    rcases (hS p hp).dvd_mul.mp hdvd with h' | h'
    · exact hm p hp h'
    · exact hn p hp h'
end DeletedPrimes
