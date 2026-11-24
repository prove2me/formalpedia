-- Prove2me | solution 1 for DeletedPrimes.near_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:17:32.701396+00:00
-- url     : https://prove2.me/submissions/c5d1b7dd-5515-4218-8185-1a5680f2d924

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity

set_option autoImplicit false
open Real
open DeletedPrimes
open Classical
namespace DeletedPrimes
theorem _root_.solution {q k k' a : ℤ} (hq : 0 < q) (hk : 2 * |k * q - a| < q)
    (hk' : 2 * |k' * q - a| < q) : k = k' := by
  have h1 := le_abs_self (k * q - a)
  have h2 := neg_abs_le (k * q - a)
  have h3 := le_abs_self (k' * q - a)
  have h4 := neg_abs_le (k' * q - a)
  rcases lt_trichotomy k k' with h | h | h
  · have : (k' - k) * q ≥ 1 * q := mul_le_mul_of_nonneg_right (by omega) hq.le
    nlinarith
  · exact h
  · have : (k - k') * q ≥ 1 * q := mul_le_mul_of_nonneg_right (by omega) hq.le
    nlinarith
end DeletedPrimes
