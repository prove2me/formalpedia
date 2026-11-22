-- Prove2me | solution 1 for Bernstein.exists_ne_zero_equation_y_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T17:32:04.981778+00:00
-- url     : https://prove2.me/submissions/64b866fe-aa1a-44b1-81f1-523c007b00e5

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein.Readings

open WeierstrassCurve

/-- Every element of `F_p` is a square in `F_{p²}` (odd `p`), by Euler's criterion. -/
theorem isSquare_emb (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : ZMod p) :
    IsSquare (emb p a) := by
  by_cases ha : a = 0
  · subst ha; simp
  let _ : Fintype (Fp2 p) := Fintype.ofFinite _
  have hcard : Fintype.card (Fp2 p) = p ^ 2 := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card p 2 (by norm_num)
  have hchar : ringChar (Fp2 p) ≠ 2 := by
    rw [ringChar.eq (Fp2 p) p]; omega
  have hne : emb p a ≠ 0 := by simpa using ha
  rw [FiniteField.isSquare_iff hchar hne, hcard]
  obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd' with h | ⟨k, hk⟩
    · omega
    · exact ⟨k, hk⟩
  have he : p ^ 2 / 2 = (p - 1) * (k + 1) := by
    subst hk
    have : (2 * k + 1) ^ 2 = 2 * ((2 * k + 1 - 1) * (k + 1)) + 1 := by
      rw [show 2 * k + 1 - 1 = 2 * k by omega]; ring
    omega
  rw [he, ← map_pow, pow_mul, ZMod.pow_card_sub_one_eq_one ha]
  simp

theorem main (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (A : ℤ)
    (_hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) :
    ∃ x : Fp2 p, x ≠ 0 ∧ (Ecurve p A).Equation x 0 := by
  obtain ⟨r, hr⟩ := isSquare_emb p hp ((A : ZMod p) ^ 2 - 4)
  have h2 : (2 : Fp2 p) ≠ 0 := by
    have := ringChar.eq (Fp2 p) p
    intro h
    have h2' : ((2 : ℕ) : Fp2 p) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (Fp2 p) p] at h2'
    have := Nat.le_of_dvd (by norm_num) h2'
    omega
  set a : Fp2 p := (A : Fp2 p) with ha
  have hr' : a ^ 2 - 4 = r * r := by
    rw [← hr, ha]; simp [map_ofNat]
  set x : Fp2 p := (-a + r) / 2 with hx
  have hq : x ^ 2 + a * x + 1 = 0 := by
    rw [hx]; field_simp
    linear_combination (-1 : Fp2 p) * hr'
  refine ⟨x, ?_, ?_⟩
  · intro h0; rw [h0] at hq; simp at hq
  · rw [Affine.equation_iff]
    simp [Ecurve, curve, WeierstrassCurve.baseChange, WeierstrassCurve.map]
    rw [ha] at hq
    linear_combination (-x) * hq
end Bernstein.Readings

open Bernstein in
theorem solution (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) :
    ∃ x : Fp2 p, x ≠ 0 ∧ (Ecurve p A).Equation x 0 :=
  Bernstein.Readings.main p hp A hA
