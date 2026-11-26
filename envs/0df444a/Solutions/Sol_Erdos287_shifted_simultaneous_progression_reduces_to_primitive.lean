-- Prove2me | solution 1 for Erdos287.shifted_simultaneous_progression_reduces_to_primitive
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T19:56:05.422866+00:00
-- url     : https://prove2.me/submissions/3b58cc91-f9ec-4750-884b-2dd64bf3c6ee

import Mathlib

set_option autoImplicit false

private theorem gcd_eq_of_modEq {q x y : ℤ} (h : x ≡ y [ZMOD q]) :
    x.gcd q = y.gcd q := by
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp h
  have hy : y = x + q * t := by linarith only [ht]
  calc
    x.gcd q = q.gcd x := Int.gcd_comm _ _
    _ = q.gcd (x + q * t) := (Int.gcd_add_mul_left_right q x t).symm
    _ = y.gcd q := by rw [← hy, Int.gcd_comm]

/-- Dividing a shifted simultaneous progression by its known modulus
and its exact common divisor gives a primitive progression. -/
theorem solution (m q s n a A : ℤ) (hmq : 0 < m * q) (hs : s ≠ 0)
    (hcop : IsCoprime m q) (hscop : IsCoprime s (m * q))
    (hdiv : s ∣ m * n - a) (hA : m * n ≡ A [ZMOD q]) :
    let w := (m * n - a) / s
    let g : ℤ := ↑(a.gcd m * (A - a).gcd q)
    0 < g ∧ g ∣ w ∧ g ∣ m * q ∧ IsCoprime (w / g) (m * q / g) ∧
      ∀ t : ℤ, (m * (n + q * s * t) - a) / s / g =
        w / g + (m * q / g) * t := by
  intro w g
  have hw : s * w = m * n - a := Int.mul_ediv_cancel' hdiv
  have hdivM : (m * n - a).gcd m = a.gcd m := by
    have hm : m * n - a ≡ -a [ZMOD m] := Int.modEq_iff_dvd.mpr ⟨-n, by ring⟩
    rw [gcd_eq_of_modEq hm, Int.gcd_comm (-a) m, Int.gcd_neg, Int.gcd_comm]
  have hdivQ : (m * n - a).gcd q = (A - a).gcd q :=
    gcd_eq_of_modEq (hA.sub (Int.ModEq.refl a))
  have hproduct : (m * n - a).gcd (m * q) =
      (m * n - a).gcd m * (m * n - a).gcd q := by
    simpa only [Int.gcd_def, Int.natAbs_mul] using
      (Int.isCoprime_iff_nat_coprime.mp hcop).gcd_mul (m * n - a).natAbs
  have hcancel : (s * w).gcd (m * q) = w.gcd (m * q) := by
    rw [Int.gcd_comm (s * w), Int.gcd_comm w, Int.gcd_def, Int.gcd_def, Int.natAbs_mul s]
    exact (Int.isCoprime_iff_nat_coprime.mp hscop).gcd_mul_left_cancel_right w.natAbs
  have hG : (↑(w.gcd (m * q)) : ℤ) = g := by
    rw [← hcancel, hw, hproduct, hdivM, hdivQ]
  have hnat : 0 < w.gcd (m * q) := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hmq.ne' ((Int.gcd_eq_zero_iff.mp hz).2)
  have hg : 0 < g := by
    rw [← hG]
    exact_mod_cast hnat
  have hgw : g ∣ w := hG ▸ Int.gcd_dvd_left w (m * q)
  have hgd : g ∣ m * q := hG ▸ Int.gcd_dvd_right w (m * q)
  refine ⟨hg, hgw, hgd, ?_, ?_⟩
  · rw [← hG, Int.isCoprime_iff_gcd_eq_one]
    exact Int.gcd_ediv_gcd_ediv_gcd hnat
  · intro t
    have hshift : (m * (n + q * s * t) - a) / s = w + m * q * t := by
      apply Int.ediv_eq_of_eq_mul_left hs
      calc
        _ = (m * n - a) + m * q * s * t := by ring
        _ = _ := by rw [← hw]; ring
    rw [hshift]
    apply Int.ediv_eq_of_eq_mul_left hg.ne'
    calc
      _ = g * (w / g) + g * (m * q / g) * t := by
        rw [Int.mul_ediv_cancel' hgw, Int.mul_ediv_cancel' hgd]
      _ = _ := by ring

