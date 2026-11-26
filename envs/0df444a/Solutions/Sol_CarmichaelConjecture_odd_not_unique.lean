-- Prove2me | solution 1 for CarmichaelConjecture.odd_not_unique
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:41:47.349564+00:00
-- url     : https://prove2.me/submissions/9022ae67-315d-4846-93d5-df2307517526

import Mathlib
namespace CarmichaelConjecture
theorem _root_.solution {n : Nat} (hn : Odd n) :
    ∃ m, m ≠ n ∧ Nat.totient m = Nat.totient n := by
  refine ⟨2 * n, ?_, ?_⟩
  · have : 0 < n := hn.pos
    omega
  · rw [Nat.totient_mul (Nat.coprime_two_left.mpr hn), Nat.totient_two, one_mul]

end CarmichaelConjecture

