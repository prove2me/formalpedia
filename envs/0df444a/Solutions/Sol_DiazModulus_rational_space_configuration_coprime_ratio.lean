-- Prove2me | solution 1 for DiazModulus.rational_space_configuration_coprime_ratio
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:27:27.82675+00:00
-- url     : https://prove2.me/submissions/414886de-648b-40aa-acf9-75bf41f12593

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The ratio of a configuration in a subspace of `Q̄(u)` is a coprime quotient `p(u)/q(u)`

Both `x₀ y₀` and `x₁ y₀` lie in `W ⊆ Q̄(u)`, and `x₀, y₀ ≠ 0` because the families are free, so
`x₁/x₀ = (x₁ y₀)/(x₀ y₀)` lies in the field `Q̄(u)`. By `IntermediateField.mem_adjoin_simple_iff`
it is `r(u)/s(u)` for polynomials `r, s` over `Q̄`; `s(u) ≠ 0`, since otherwise `x₁/x₀ = 0`.
Dividing `r` and `s` by `g = gcd(r, s)` gives coprime `p = r/g`, `q = s/g`
(`isCoprime_div_gcd_div_gcd`), and `x₁ q(u) = x₀ p(u)` after cancelling `g(u)`, which is not zero
because `u` is transcendental over `Q̄`. If `p` and `q` were both constants `a`, `b`, then
`a x₀ - b x₁ = 0` would force `a = b = 0` by the freeness of `x`, and `0, 0` are not coprime; so
`max(deg p, deg q) ≥ 1`.
-/

namespace R20_C15

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem aeval_injective {u : ℂ} (hu : u ∉ Qbar) :
    Function.Injective (aeval (R := ↥Qbar) u) :=
  (injective_iff_map_eq_zero _).2 fun P hP => transcendental_iff.1 (tr_of_not_mem hu) P hP

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem smul_eq (a : ↥Qbar) (z : ℂ) : a • z = (a : ℂ) * z := rfl

end R20_C15

open DiazModulus R20_C15 Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ)
    (hrat : ∀ w ∈ W, w ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ))
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) (hxy : ∀ i j, x i * y j ∈ W) :
    ∃ p q : (↥Qbar)[X], IsCoprime p q ∧ 1 ≤ max p.natDegree q.natDegree ∧
      x 1 * aeval u q = x 0 * aeval u p := by
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  have hx1 : x 1 ≠ 0 := hx.ne_zero 1
  have hy0 : y 0 ≠ 0 := hy.ne_zero 0
  have hmem : x 1 / x 0 ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ) := by
    have h := div_mem (hrat _ (hxy 1 0)) (hrat _ (hxy 0 0))
    rwa [mul_div_mul_right _ _ hy0] at h
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff _ _).1 hmem
  have hsu : aeval u s ≠ 0 := by
    intro h0
    rw [h0, div_zero, div_eq_zero_iff] at hrs
    exact hrs.elim hx1 hx0
  have hs0 : s ≠ 0 := by rintro rfl; exact hsu (map_zero _)
  have hrel : x 1 * aeval u s = x 0 * aeval u r := by
    rw [div_eq_div_iff hx0 hsu] at hrs
    linear_combination hrs
  have hg0 : GCDMonoid.gcd r s ≠ 0 := gcd_ne_zero_of_right hs0
  have hgu : aeval u (GCDMonoid.gcd r s) ≠ 0 := fun h0 =>
    hg0 (aeval_injective hu (by rw [h0, map_zero]))
  have er : aeval u r = aeval u (GCDMonoid.gcd r s) * aeval u (r / GCDMonoid.gcd r s) := by
    rw [← map_mul, EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left r s)]
  have es : aeval u s = aeval u (GCDMonoid.gcd r s) * aeval u (s / GCDMonoid.gcd r s) := by
    rw [← map_mul, EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right r s)]
  have hcop := isCoprime_div_gcd_div_gcd (p := r) hs0
  have hrel' : x 1 * aeval u (s / GCDMonoid.gcd r s) = x 0 * aeval u (r / GCDMonoid.gcd r s) := by
    apply mul_left_cancel₀ hgu
    rw [er, es] at hrel
    linear_combination hrel
  refine ⟨_, _, hcop, ?_, hrel'⟩
  by_contra hlt
  have hp := eq_C_of_natDegree_eq_zero (p := r / GCDMonoid.gcd r s) (by omega)
  have hq := eq_C_of_natDegree_eq_zero (p := s / GCDMonoid.gcd r s) (by omega)
  rw [hp, hq, aeval_C, aeval_C, am, am] at hrel'
  have hxv : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rw [hxv] at hx
  obtain ⟨ha, hb⟩ := LinearIndependent.pair_iff.1 hx ((r / GCDMonoid.gcd r s).coeff 0)
    (-(s / GCDMonoid.gcd r s).coeff 0) (by
      rw [neg_smul, smul_eq, smul_eq]
      linear_combination -hrel')
  rw [neg_eq_zero] at hb
  rw [hp, hq, ha, hb, map_zero] at hcop
  exact not_isCoprime_zero_zero hcop
