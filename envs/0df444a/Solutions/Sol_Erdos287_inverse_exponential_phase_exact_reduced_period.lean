-- Prove2me | solution 1 for Erdos287.inverse_exponential_phase_exact_reduced_period
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T15:57:07.094799+00:00
-- url     : https://prove2.me/submissions/506b5b5c-e1f5-4266-9814-8ab64363581d

import Mathlib

set_option autoImplicit false

private theorem inverse_congruent {q x y u v : ℤ}
    (hx : x * u ≡ 1 [ZMOD q]) (hy : y * v ≡ 1 [ZMOD q])
    (hxy : x ≡ y [ZMOD q]) : u ≡ v [ZMOD q] := by
  calc
    u ≡ (y * v) * u [ZMOD q] := by simpa using hy.symm.mul_right u
    _ = (y * u) * v := by ring
    _ ≡ (x * u) * v [ZMOD q] := (hxy.symm.mul_right u).mul_right v
    _ ≡ v [ZMOD q] := by simpa using hx.mul_right v

/-- The phase of a modular inverse on unit arguments has the exact reduced
period obtained by dividing the coefficient and the modulus by their gcd. -/
theorem solution (a m x y u v : ℤ) (hm : 0 < m)
    (hx : x * u ≡ 1 [ZMOD m]) (hy : y * v ≡ 1 [ZMOD m]) :
    let g : ℤ := Int.gcd a m
    let q := m / g
    let b := a / g
    Int.gcd b q = 1 ∧ ((a * u ≡ a * v [ZMOD m]) ↔ (x ≡ y [ZMOD q])) := by
  intro g q b
  have hgNat : 0 < Int.gcd a m := Int.gcd_pos_of_ne_zero_right a hm.ne'
  have hg : g ≠ 0 := by
    change (Int.gcd a m : ℤ) ≠ 0
    exact_mod_cast hgNat.ne'
  have hq : g * q = m := Int.mul_ediv_cancel' (Int.gcd_dvd_right a m)
  have hb : g * b = a := Int.mul_ediv_cancel' (Int.gcd_dvd_left a m)
  have hbq : Int.gcd b q = 1 := Int.gcd_ediv_gcd_ediv_gcd hgNat
  have hxq : x * u ≡ 1 [ZMOD q] := hx.of_dvd ⟨g, by simpa [mul_comm] using hq.symm⟩
  have hyq : y * v ≡ 1 [ZMOD q] := hy.of_dvd ⟨g, by simpa [mul_comm] using hq.symm⟩
  have hunit : b * Int.gcdA b q ≡ 1 [ZMOD q] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨Int.gcdB b q, ?_⟩
    have hBez := Int.gcd_eq_gcd_ab b q
    rw [hbq] at hBez
    norm_num at hBez
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hBez)
  have hcancel : (a * u ≡ a * v [ZMOD m]) ↔ (b * u ≡ b * v [ZMOD q]) := by
    simpa only [← mul_assoc, hb, hq] using
      (Int.ModEq.mul_left_cancel_iff' (a := b * u) (b := b * v) (m := q) hg)
  refine ⟨hbq, ?_⟩
  rw [hcancel]
  constructor
  · intro huv
    have huv' : u ≡ v [ZMOD q] := calc
      u ≡ (b * Int.gcdA b q) * u [ZMOD q] := by simpa using hunit.symm.mul_right u
      _ = (b * u) * Int.gcdA b q := by ring
      _ ≡ (b * v) * Int.gcdA b q [ZMOD q] := huv.mul_right _
      _ = (b * Int.gcdA b q) * v := by ring
      _ ≡ v [ZMOD q] := by simpa using hunit.mul_right v
    exact inverse_congruent (by simpa [mul_comm] using hxq)
      (by simpa [mul_comm] using hyq) huv'
  · intro hxy
    exact (inverse_congruent hxq hyq hxy).mul_left b

