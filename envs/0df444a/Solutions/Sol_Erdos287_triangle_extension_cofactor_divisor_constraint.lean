-- Prove2me | solution 1 for Erdos287.triangle_extension_cofactor_divisor_constraint
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:07:40.243228+00:00
-- url     : https://prove2.me/submissions/d51f3048-8277-4fbc-bb99-6cb11707e280

import Mathlib

set_option autoImplicit false

private theorem cross_gcd (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (hcd : c.Coprime d) :
    Nat.gcd (c * b) (a * d) = Nat.gcd a c * Nat.gcd b d := by
  let g := Nat.gcd a c
  let h := Nat.gcd b d
  let a' := a / g
  let b' := b / h
  let c' := c / g
  let d' := d / h
  have hp : 0 < g := Nat.gcd_pos_of_pos_left c ha
  have hq : 0 < h := Nat.gcd_pos_of_pos_left d hb
  have ha' : a' * g = a := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hb' : b' * h = b := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hc' : c' * g = c := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have hd' : d' * h = d := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have hac' : a'.Coprime c' := Nat.coprime_div_gcd_div_gcd hp
  have hbd' : b'.Coprime d' := Nat.coprime_div_gcd_div_gcd hq
  have hab' : a'.Coprime b' :=
    (hab.coprime_dvd_left ⟨g, ha'.symm⟩).coprime_dvd_right ⟨h, hb'.symm⟩
  have hcd' : c'.Coprime d' :=
    (hcd.coprime_dvd_left ⟨g, hc'.symm⟩).coprime_dvd_right ⟨h, hd'.symm⟩
  have hcop : (c' * b').Coprime (a' * d') :=
    Nat.coprime_mul_iff_left.mpr ⟨hac'.symm.mul_right hcd', hab'.symm.mul_right hbd'⟩
  have hleft : c * b = (g * h) * (c' * b') := by rw [← hc', ← hb']; ring
  have hright : a * d = (g * h) * (a' * d') := by rw [← ha', ← hd']; ring
  rw [hleft, hright, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]

/-- With one adjacency fixed, the other outgoing cofactor in a balanced
triangle is determined up to signs by divisors of the fixed cofactors. -/
theorem solution (a b c d e f : ℕ) (x y z ε η θ : ℤ)
    (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (hab : a.Coprime b) (hcd : c.Coprime d) (hef : e.Coprime f)
    (hbalance : e * (a * d) = f * (c * b))
    (hxy : (a : ℤ) * x - (b : ℤ) * y = ε)
    (hxz : (c : ℤ) * x - (d : ℤ) * z = η)
    (hyz : (e : ℤ) * y - (f : ℤ) * z = θ) (hθ : |θ| = 1) :
    |((a / Nat.gcd a c : ℕ) : ℤ) * η - ((c / Nat.gcd a c : ℕ) : ℤ) * ε|
      = ↑(Nat.gcd b d) := by
  let g := Nat.gcd a c
  let h := Nat.gcd b d
  have hg : 0 < g := Nat.gcd_pos_of_pos_left c ha
  have hfdvd : e ∣ f * (c * b) := by rw [← hbalance]; exact dvd_mul_right e (a * d)
  have hdvd : e ∣ c * b := hef.dvd_of_dvd_mul_left hfdvd
  obtain ⟨k, hk⟩ := hdvd
  have hk' : a * d = f * k := by
    apply Nat.eq_of_mul_eq_mul_left he
    calc
      e * (a * d) = f * (c * b) := hbalance
      _ = e * (f * k) := by rw [hk]; ring
  have heq : k = g * h := by
    have h1 : Nat.gcd (c * b) (a * d) = k := by
      rw [hk, hk', Nat.gcd_mul_right, hef.gcd_eq_one, one_mul]
    exact h1.symm.trans (cross_gcd a b c d ha hb hab hcd)
  have hk₁ : (e : ℤ) * k = (c : ℤ) * b := by exact_mod_cast hk.symm
  have hk₂ : (f : ℤ) * k = (a : ℤ) * d := by exact_mod_cast hk'.symm
  have h₁ : (c : ℤ) * b * y - (a : ℤ) * d * z = (k : ℤ) * θ := by
    rw [← hk₁, ← hk₂]
    linear_combination (k : ℤ) * hyz
  have h₂ : (a : ℤ) * η - (c : ℤ) * ε = (k : ℤ) * θ := by
    linear_combination h₁ + (c : ℤ) * hxy - (a : ℤ) * hxz
  have ha₀ : (g : ℤ) * ((a / g : ℕ) : ℤ) = a := by
    have h : (a / g) * g = a := Nat.div_mul_cancel (Nat.gcd_dvd_left a c)
    rw [mul_comm]
    exact_mod_cast h
  have hc₀ : (g : ℤ) * ((c / g : ℕ) : ℤ) = c := by
    have h : (c / g) * g = c := Nat.div_mul_cancel (Nat.gcd_dvd_right a c)
    rw [mul_comm]
    exact_mod_cast h
  have hh : (k : ℤ) = (g : ℤ) * h := by exact_mod_cast heq
  have h₃ : ((a / g : ℕ) : ℤ) * η - ((c / g : ℕ) : ℤ) * ε = (h : ℤ) * θ := by
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hg.ne')
    linear_combination h₂ + η * ha₀ - ε * hc₀ + θ * hh
  change |((a / g : ℕ) : ℤ) * η - ((c / g : ℕ) : ℤ) * ε| = (h : ℤ)
  rw [h₃, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ h), hθ, mul_one]

