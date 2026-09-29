-- Prove2me | solution 1 for GelfondSchneider.rho_denominator
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:06:25.754721+00:00
-- url     : https://prove2.me/submissions/28fd5885-6060-4c33-a0be-c94bb4fb263a

import Mathlib

open NumberField

namespace GS_rhoden

/-- A common nonzero integer denominator for three elements of a number field. -/
lemma exists_common_denom {K : Type*} [Field K] [NumberField K] (α β γ : K) :
    ∃ c : ℤ, c ≠ 0 ∧ IsIntegral ℤ ((c : K) * α) ∧ IsIntegral ℤ ((c : K) * β) ∧
      IsIntegral ℤ ((c : K) * γ) := by
  classical
  obtain ⟨y, hy, hf⟩ := exists_integral_multiples ℤ ℚ (L := K) {α, β, γ}
  refine ⟨y, hy, ?_, ?_, ?_⟩
  · have h := hf α (by simp)
    rwa [zsmul_eq_mul] at h
  · have h := hf β (by simp)
    rwa [zsmul_eq_mul] at h
  · have h := hf γ (by simp)
    rwa [zsmul_eq_mul] at h

/-- Raising the power of an integer factor preserves integrality. -/
lemma isIntegral_pow_mul_of_le {K : Type*} [Field K] (c : ℤ) (x : K) {E N : ℕ}
    (hEN : E ≤ N) (h : IsIntegral ℤ ((c : K) ^ E * x)) :
    IsIntegral ℤ ((c : K) ^ N * x) := by
  have hsplit : (c : K) ^ N * x = (c : K) ^ (N - E) * ((c : K) ^ E * x) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hEN]
  rw [hsplit]
  exact ((isIntegral_intCast c).pow (N - E)).mul h

/-- One term of the sum, cleared by `c ^ (r + A + B)`, is integral. -/
lemma term_isIntegral {K : Type*} [Field K] (c : ℤ) (α β γ : K)
    (hα : IsIntegral ℤ ((c : K) * α)) (hβ : IsIntegral ℤ ((c : K) * β))
    (hγ : IsIntegral ℤ ((c : K) * γ)) (e : K) (he : IsIntegral ℤ e) (a b r A B : ℕ) :
    IsIntegral ℤ ((c : K) ^ (r + A + B) *
      (e * (((a : K) + 1) + ((b : K) + 1) * β) ^ r * α ^ A * γ ^ B)) := by
  have hX : IsIntegral ℤ ((c : K) * (((a : K) + 1) + ((b : K) + 1) * β)) := by
    have hrw : (c : K) * (((a : K) + 1) + ((b : K) + 1) * β) =
        (c : K) * ((a : K) + 1) + ((b : K) + 1) * ((c : K) * β) := by ring
    rw [hrw]
    refine IsIntegral.add ((isIntegral_intCast c).mul
      ((isIntegral_natCast a).add isIntegral_one)) ?_
    exact ((isIntegral_natCast b).add isIntegral_one).mul hβ
  have hrw : (c : K) ^ (r + A + B) *
      (e * (((a : K) + 1) + ((b : K) + 1) * β) ^ r * α ^ A * γ ^ B) =
      e * ((c : K) * (((a : K) + 1) + ((b : K) + 1) * β)) ^ r * ((c : K) * α) ^ A *
        ((c : K) * γ) ^ B := by
    rw [mul_pow, mul_pow, mul_pow]
    ring
  rw [hrw]
  exact ((he.mul (hX.pow r)).mul (hα.pow A)).mul (hγ.pow B)

/-- The exponent bound: `r + (a+1) l₀ + (b+1) l₀ ≤ (1 + 4 m²) r`. -/
lemma exponent_le (m n q r l₀ a b : ℕ) (hq : q ^ 2 = 2 * m * n) (hnr : n ≤ r)
    (hlm : l₀ ≤ m) (ha : a < q) (hb : b < q) :
    r + (a + 1) * l₀ + (b + 1) * l₀ ≤ (1 + 4 * m ^ 2) * r := by
  have hqr : q ≤ 2 * m * r :=
    calc q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
      _ = 2 * m * n := hq
      _ ≤ 2 * m * r := Nat.mul_le_mul_left _ hnr
  have h1 : (a + 1) * l₀ ≤ q * m := Nat.mul_le_mul (Nat.succ_le_of_lt ha) hlm
  have h2 : (b + 1) * l₀ ≤ q * m := Nat.mul_le_mul (Nat.succ_le_of_lt hb) hlm
  have h3 : q * m ≤ 2 * m * r * m := Nat.mul_le_mul_right m hqr
  have h4 : (1 + 4 * m ^ 2) * r = r + 2 * (2 * m * r * m) := by ring
  rw [h4]
  omega

end GS_rhoden

open GS_rhoden in
theorem solution (K : Type*) [Field K] [NumberField K] (α' β' γ' : K)
    (m : ℕ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ (n q r l₀ : ℕ) (η : Fin q → Fin q → 𝓞 K),
      0 < n → q ^ 2 = 2 * m * n → n ≤ r → 1 ≤ l₀ → l₀ ≤ m →
      IsIntegral ℤ ((D : K) ^ r * ∑ a : Fin q, ∑ b : Fin q, (η a b : K) *
          (((a : ℕ) + 1 : K) + ((b : ℕ) + 1 : K) * β') ^ r *
          α' ^ (((a : ℕ) + 1) * l₀) * γ' ^ (((b : ℕ) + 1) * l₀)) := by
  obtain ⟨c, hc0, hα, hβ, hγ⟩ := exists_common_denom α' β' γ'
  refine ⟨c ^ (1 + 4 * m ^ 2), pow_ne_zero _ hc0, ?_⟩
  intro n q r l₀ η _hn hq hnr _hl1 hlm
  rw [Int.cast_pow, ← pow_mul, Finset.mul_sum]
  refine IsIntegral.sum _ (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine IsIntegral.sum _ (fun b _ => ?_)
  refine isIntegral_pow_mul_of_le c _
    (exponent_le m n q r l₀ (a : ℕ) (b : ℕ) hq hnr hlm a.isLt b.isLt) ?_
  exact term_isIntegral c α' β' γ' hα hβ hγ _ (RingOfIntegers.isIntegral_coe (η a b))
    _ _ _ _ _

#print axioms solution
