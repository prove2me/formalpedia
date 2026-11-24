-- Prove2me | solution 1 for DeletedPrimes.card_window_dvd_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:06:33.72491+00:00
-- url     : https://prove2.me/submissions/af6589f1-a673-48d2-af84-74ec42f926fb

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity

set_option autoImplicit false
open Real
open DeletedPrimes
open Classical
namespace DeletedPrimes
theorem _root_.solution (n : ℤ) (J q : ℕ) (hq : 0 < q) :
    ((Finset.Icc (-(J : ℤ)) J).filter (fun j => (q : ℤ) ∣ n + j)).card ≤ 2 * J / q + 1 := by
  set S := (Finset.Icc (-(J : ℤ)) J).filter (fun j => (q : ℤ) ∣ n + j)
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hmap : Set.MapsTo (fun j : ℤ => ((j + J) / q).toNat) (S : Set ℤ)
      (Finset.range (2 * J / q + 1) : Set ℕ) := by
    intro j hj
    simp only [S, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hj
    simp only [Finset.coe_range, Set.mem_Iio]
    have h1 : (j + J) / (q : ℤ) ≤ (2 * J : ℤ) / (q : ℤ) :=
      Int.ediv_le_ediv hqz (by omega)
    have h2 : ((2 * J : ℤ) / (q : ℤ)) = ((2 * J / q : ℕ) : ℤ) := by push_cast; rfl
    have h3 : 0 ≤ (j + J) / (q : ℤ) := Int.ediv_nonneg (by omega) hqz.le
    omega
  have hinj : Set.InjOn (fun j : ℤ => ((j + J) / q).toNat) (S : Set ℤ) := by
    intro a ha b hb hab
    simp only [S, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at ha hb
    simp only at hab
    have ha0 : 0 ≤ (a + J) / (q : ℤ) := Int.ediv_nonneg (by omega) hqz.le
    have hb0 : 0 ≤ (b + J) / (q : ℤ) := Int.ediv_nonneg (by omega) hqz.le
    have hdiv : (a + J) / (q : ℤ) = (b + J) / (q : ℤ) := by omega
    have hmod : (a + J) % (q : ℤ) = (b + J) % (q : ℤ) := by
      have : (a + J) ≡ (b + J) [ZMOD q] := by
        rw [Int.modEq_iff_dvd]
        have := dvd_sub hb.2 ha.2
        have e : n + b - (n + a) = b + J - (a + J) := by ring
        rw [e] at this; exact this
      exact this
    have ea := Int.mul_ediv_add_emod (a + J) q
    have eb := Int.mul_ediv_add_emod (b + J) q
    rw [hdiv, hmod] at ea
    omega
  calc S.card ≤ (Finset.range (2 * J / q + 1)).card := Finset.card_le_card_of_injOn _ hmap hinj
    _ = 2 * J / q + 1 := Finset.card_range _
end DeletedPrimes
