-- Prove2me | solution 1 for DeletedPrimes.card_primes_dvd_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:05:37.913907+00:00
-- url     : https://prove2.me/submissions/1f3ed0eb-eace-4aba-a10d-7c39ff4af24b

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity

set_option autoImplicit false
open Real
open DeletedPrimes
open Classical
namespace DeletedPrimes
theorem _root_.solution {T : Finset ℕ} {Y L : ℕ} {N : ℤ} (hY2 : 2 ≤ Y) (hN : N ≠ 0)
    (hNb : N.natAbs < Y ^ (L + 1)) (hp : ∀ q ∈ T, q.Prime) (hY : ∀ q ∈ T, Y ≤ q)
    (hd : ∀ q ∈ T, (q : ℤ) ∣ N) : T.card ≤ L := by
  have hpos : 0 < N.natAbs := Int.natAbs_pos.mpr hN
  have hprod : (∏ q ∈ T, q) ∣ N.natAbs :=
    Finset.prod_primes_dvd N.natAbs (fun q hq => (hp q hq).prime)
      (fun q hq => Int.natCast_dvd.mp (hd q hq))
  have h1 : Y ^ T.card ≤ ∏ q ∈ T, q := by
    have := Finset.pow_card_le_prod T (fun q => q) Y hY
    simpa using this
  have hle : Y ^ T.card ≤ N.natAbs := le_trans h1 (Nat.le_of_dvd hpos hprod)
  have hlt : Y ^ T.card < Y ^ (L + 1) := lt_of_le_of_lt hle hNb
  have := (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
  omega
end DeletedPrimes
