-- Prove2me | solution 1 for Erdos287.middle_affine_forms_inject_into_cofactor_divisors
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T19:13:51.844979+00:00
-- url     : https://prove2.me/submissions/18650444-b808-4664-be9f-8453a6295b5b

import Mathlib

open Finset

set_option autoImplicit false

private theorem middle_relation (a b c A B C u y x z v w : ℤ)
    (ha : a ≠ 0) (hx : 0 < x) (hy : 0 < y) (hv : 0 < v) (hw : 0 < w)
    (hl₁ : u * a = y * b) (hl₂ : x * b = z * c) (hl₃ : v * a = w * c)
    (hc₁ : y * B = u * A + 1) (hc₂ : z * C = x * B + 1) (hc₃ : w * C = v * A + 1) :
    0 < u - v ∧ z * (u - v) = w * u := by
  have hcross : y * z * v = w * x * u := by
    apply mul_right_cancel₀ ha
    linear_combination (y * z) * hl₃ - (w * x) * hl₁ - (y * w) * hl₂
  have hfirst : w * (x + y) = y * z := by
    linear_combination (y * z) * hc₃ - (w * y) * hc₂ - (w * x) * hc₁ + A * hcross
  have hsecond : v * (x + y) = x * u := by
    apply mul_left_cancel₀ hw.ne'
    linear_combination v * hfirst + hcross
  have hdiff : x * (u - v) = v * y := by linear_combination -hsecond
  have hp : 0 < x * (u - v) := hdiff.symm ▸ mul_pos hv hy
  refine ⟨pos_of_mul_pos_right hp hx.le, ?_⟩
  apply mul_left_cancel₀ hy.ne'
  linear_combination -(u - v) * hfirst + w * hdiff

/-- Fix the endpoint edge of an oriented triangle of primitive affine
forms. Every middle form determines a different divisor of the product
of the endpoint cofactors, with the displayed cap and ratio constraints. -/
theorem solution (mid : Finset (ℕ × ℕ)) (a A c C v w cap : ℕ)
    (ha : 0 < a) (hv : 0 < v) (hw : 0 < w)
    (hl : v * a = w * c) (hc : w * C = v * A + 1)
    (hprimitive : ∀ p ∈ mid, p.1.Coprime p.2)
    (hedge : ∀ p ∈ mid, ∃ u y x z : ℕ,
      0 < x ∧ 0 < y ∧ u ≤ cap ∧ z ≤ cap ∧ 4 * u < 11 * v ∧ 4 * z < 11 * w ∧
      u * a = y * p.1 ∧ x * p.1 = z * c ∧ y * p.2 = u * A + 1 ∧ z * C = x * p.2 + 1) :
    mid.card ≤ ((v * w).divisors.filter (fun d =>
      v + d ≤ cap ∧ v * w ≤ (cap - w) * d ∧ 4 * d < 7 * v ∧ 4 * v < 7 * d)).card := by
  classical
  choose! u y x z hx hy hu hz hru hrz hl₁ hl₂ hc₁ hc₂ using hedge
  let code (p : ℕ × ℕ) := u p - v
  let allowed := (v * w).divisors.filter (fun d =>
    v + d ≤ cap ∧ v * w ≤ (cap - w) * d ∧ 4 * d < 7 * v ∧ 4 * v < 7 * d)
  have hstep (p : ℕ × ℕ) (hp : p ∈ mid) :
      0 < code p ∧ v + code p = u p ∧ (z p - w) * code p = v * w ∧
        z p * code p = w * (v + code p) := by
    have hi := middle_relation a p.1 c A p.2 C (u p) (y p) (x p) (z p) v w
      (by exact_mod_cast ha.ne') (by exact_mod_cast hx p hp) (by exact_mod_cast hy p hp)
      (by exact_mod_cast hv) (by exact_mod_cast hw)
      (by exact_mod_cast hl₁ p hp) (by exact_mod_cast hl₂ p hp) (by exact_mod_cast hl)
      (by exact_mod_cast hc₁ p hp) (by exact_mod_cast hc₂ p hp) (by exact_mod_cast hc)
    have hvu : v ≤ u p := by omega
    have hs : v + code p = u p := by dsimp [code]; omega
    have hd : 0 < code p := by dsimp [code]; omega
    have hprod : z p * code p = w * (v + code p) := by
      rw [hs]
      apply Int.natCast_inj.mp
      push_cast [code, hvu]
      exact hi.2
    refine ⟨hd, hs, ?_, hprod⟩
    rw [Nat.sub_mul, hprod, Nat.mul_add, Nat.add_sub_cancel, Nat.mul_comm]
  change mid.card ≤ allowed.card
  apply card_le_card_of_injOn code
  · intro p hp
    have hp' : p ∈ mid := hp
    obtain ⟨hd, hs, hdiv, hprod⟩ := hstep p hp'
    have hcompare : w * (4 * v + 4 * code p) < w * (11 * code p) := by
      calc
        w * (4 * v + 4 * code p) = (4 * z p) * code p := by
          rw [mul_assoc, hprod]
          ring
        _ < (11 * w) * code p := Nat.mul_lt_mul_of_pos_right (hrz p hp') hd
        _ = _ := by ring
    have hratio : 4 * v < 7 * code p := by
      have hcancel := Nat.lt_of_mul_lt_mul_left hcompare
      omega
    change code p ∈ allowed
    refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨z p - w, hdiv.symm.trans (Nat.mul_comm _ _)⟩,
      Nat.mul_ne_zero hv.ne' hw.ne'⟩, hs.le.trans (hu p hp'), ?_, ?_, hratio⟩
    · exact hdiv.symm.le.trans (Nat.mul_le_mul_right (code p) (Nat.sub_le_sub_right (hz p hp') w))
    · have h := hru p hp'
      omega
  · intro p hp q hq he
    have huq : u p = u q := by rw [← (hstep p hp).2.1, ← (hstep q hq).2.1, he]
    have hlin : y p * p.1 = y q * q.1 := by rw [← hl₁ p hp, ← hl₁ q hq, huq]
    have hcon : y p * p.2 = y q * q.2 := by rw [hc₁ p hp, hc₁ q hq, huq]
    have hm := congrArg₂ Nat.gcd hlin hcon
    simp only [Nat.gcd_mul_left, (hprimitive p hp).gcd_eq_one,
      (hprimitive q hq).gcd_eq_one, mul_one] at hm
    rw [← hm] at hlin hcon
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left (hy p hp) hlin) (Nat.eq_of_mul_eq_mul_left (hy p hp) hcon)

