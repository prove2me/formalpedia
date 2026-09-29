-- Prove2me | solution 1 for DiazModulus.anisotropic_relation_four_exp_barrier
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T05:05:40.2878+00:00
-- url     : https://prove2.me/submissions/ca47b9c8-4764-4a13-94d3-a117364c02ea

import Mathlib
import Theorems.Thm_DiazModulus_conj_pair_quadratic_relation_iff
import Theorems.Thm_DiazModulus_det_linear_forms_isotropic
import Theorems.Thm_DiazModulus_det_zero_linear_forms_rank_one
import Theorems.Thm_DiazModulus_pi_transcendental

open ComplexConjugate

namespace P14Rel3

/-- `π` is transcendental over `ℚ` as a real number (from the complex statement). -/
theorem pi_real_transcendental : Transcendental ℚ Real.pi := by
  have h := DiazModulus.pi_transcendental
  rw [← Complex.coe_algebraMap] at h
  exact (transcendental_algebraMap_iff (algebraMap ℝ ℂ).injective).1 h

/-- `|u|² = x² + y²` is algebraic when `u * conj u` is. -/
theorem norm_alg (u : ℂ) (hρ : IsAlgebraic ℚ (u * conj u)) :
    IsAlgebraic ℚ (u.re ^ 2 + u.im ^ 2) := by
  have h : u * conj u = algebraMap ℝ ℂ (u.re ^ 2 + u.im ^ 2) := by
    rw [Complex.mul_conj, Complex.normSq_apply, Complex.coe_algebraMap]
    push_cast
    ring
  rw [h] at hρ
  exact (isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective).1 hρ

/-- A real root of a rational quadratic polynomial with nonzero leading coefficient is algebraic. -/
theorem isAlgebraic_of_quad (θ : ℝ) (α β γ : ℚ) (hα : α ≠ 0)
    (h : (α : ℝ) * θ ^ 2 + (β : ℝ) * θ + (γ : ℝ) = 0) : IsAlgebraic ℚ θ := by
  refine ⟨Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ,
    ?_, ?_⟩
  · intro h0
    have h2 := congr_arg (fun p => Polynomial.coeff p 2) h0
    simp at h2
    exact hα h2
  · simpa using h

/-- The transcendence step. If `α y² + β π y + γ π² = 0` with `α, β, γ` rational, `y ∉ ℚ π`, and
`s ρ = 4a y² + 2e π y + c π²` with `s ρ ≠ 0` and `ρ` algebraic, then `α = β = γ = 0`. -/
theorem quad_zero (y ρ : ℝ) (him : ∀ q : ℚ, y ≠ (q : ℝ) * Real.pi) (hρ : IsAlgebraic ℚ ρ)
    (hρ0 : ρ ≠ 0) (a c e s : ℚ) (hs : s ≠ 0)
    (hF : (s : ℝ) * ρ = 4 * (a : ℝ) * y ^ 2 + 2 * (e : ℝ) * Real.pi * y + (c : ℝ) * Real.pi ^ 2)
    (α β γ : ℚ)
    (hq : (α : ℝ) * y ^ 2 + (β : ℝ) * Real.pi * y + (γ : ℝ) * Real.pi ^ 2 = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  by_cases hα : α = 0
  · subst hα
    by_cases hβ : β = 0
    · subst hβ
      refine ⟨rfl, rfl, ?_⟩
      have h1 : (γ : ℝ) * Real.pi ^ 2 = 0 := by simpa using hq
      have h2 : (γ : ℝ) = 0 := (mul_eq_zero.1 h1).resolve_right (pow_ne_zero 2 hpi)
      exact_mod_cast h2
    · exfalso
      have hβ' : (β : ℝ) ≠ 0 := by exact_mod_cast hβ
      have h1 : Real.pi * ((β : ℝ) * y + (γ : ℝ) * Real.pi) = 0 := by
        rw [Rat.cast_zero] at hq
        linear_combination hq
      have h2 : (β : ℝ) * y + (γ : ℝ) * Real.pi = 0 := (mul_eq_zero.1 h1).resolve_left hpi
      apply him (-γ / β)
      push_cast
      field_simp
      linear_combination h2
  · exfalso
    set θ := y / Real.pi with hθ
    have hy : y = θ * Real.pi := by rw [hθ, div_mul_cancel₀ y hpi]
    have hθq : (α : ℝ) * θ ^ 2 + (β : ℝ) * θ + (γ : ℝ) = 0 := by
      have h1 : Real.pi ^ 2 * ((α : ℝ) * θ ^ 2 + (β : ℝ) * θ + (γ : ℝ)) = 0 := by
        rw [hy] at hq
        linear_combination hq
      exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero 2 hpi)
    have hθalg : IsAlgebraic ℚ θ := isAlgebraic_of_quad θ α β γ hα hθq
    set κ := ((4 * a : ℚ) : ℝ) * θ ^ 2 + ((2 * e : ℚ) : ℝ) * θ + (c : ℝ) with hκ
    have hκeq : (s : ℝ) * ρ = Real.pi ^ 2 * κ := by
      rw [hF, hy, hκ]
      push_cast
      ring
    have hsρ : (s : ℝ) * ρ ≠ 0 := mul_ne_zero (by exact_mod_cast hs) hρ0
    have hκ0 : κ ≠ 0 := by
      intro h0
      apply hsρ
      rw [hκeq, h0, mul_zero]
    have hκalg : IsAlgebraic ℚ κ :=
      (((isAlgebraic_ratCast ℚ _).mul (hθalg.pow 2)).add ((isAlgebraic_ratCast ℚ _).mul hθalg)).add
        (isAlgebraic_ratCast ℚ _)
    have hpi2 : Real.pi ^ 2 = (s : ℝ) * ρ * κ⁻¹ := by
      rw [hκeq, mul_inv_cancel_right₀ hκ0]
    have hpi2alg : IsAlgebraic ℚ (Real.pi ^ 2) := by
      rw [hpi2]
      exact ((isAlgebraic_ratCast ℚ s).mul hρ).mul hκalg.inv
    exact pi_real_transcendental (IsAlgebraic.of_pow two_pos hpi2alg)

/-- Two relations of the shape given by `conj_pair_quadratic_relation_iff`, the first with
`s = 2a + d ≠ 0`, are proportional: `s' • F = s • G` on the coefficients `a, e, c`. -/
theorem coeff_prop (y ρ : ℝ) (him : ∀ q : ℚ, y ≠ (q : ℝ) * Real.pi) (hρ : IsAlgebraic ℚ ρ)
    (hρ0 : ρ ≠ 0) (a c d e a' c' d' e' : ℚ) (hs : 2 * a + d ≠ 0)
    (hF : (2 * (a : ℝ) + d) * ρ
      = 4 * (a : ℝ) * y ^ 2 + 2 * (e : ℝ) * Real.pi * y + (c : ℝ) * Real.pi ^ 2)
    (hG : (2 * (a' : ℝ) + d') * ρ
      = 4 * (a' : ℝ) * y ^ 2 + 2 * (e' : ℝ) * Real.pi * y + (c' : ℝ) * Real.pi ^ 2) :
    (2 * a' + d') * a = (2 * a + d) * a' ∧ (2 * a' + d') * e = (2 * a + d) * e' ∧
      (2 * a' + d') * c = (2 * a + d) * c' := by
  have hF' : ((2 * a + d : ℚ) : ℝ) * ρ
      = 4 * (a : ℝ) * y ^ 2 + 2 * (e : ℝ) * Real.pi * y + (c : ℝ) * Real.pi ^ 2 := by
    push_cast
    exact hF
  have hq : ((4 * ((2 * a' + d') * a - (2 * a + d) * a') : ℚ) : ℝ) * y ^ 2
      + ((2 * ((2 * a' + d') * e - (2 * a + d) * e') : ℚ) : ℝ) * Real.pi * y
      + (((2 * a' + d') * c - (2 * a + d) * c' : ℚ) : ℝ) * Real.pi ^ 2 = 0 := by
    push_cast
    linear_combination (2 * (a : ℝ) + d) * hG - (2 * (a' : ℝ) + d') * hF
  obtain ⟨h1, h2, h3⟩ := quad_zero y ρ him hρ hρ0 a c e (2 * a + d) hs hF' _ _ _ hq
  refine ⟨?_, ?_, ?_⟩
  · linear_combination h1 / 4
  · linear_combination h2 / 2
  · linear_combination h3

/-- Coefficient of `X_k X_l` in `L₀₀ L₁₁ - L₀₁ L₁₀`. -/
def gco (A : Fin 2 → Fin 2 → Fin 3 → ℚ) (k l : Fin 3) : ℚ :=
  A 0 0 k * A 1 1 l - A 0 1 k * A 1 0 l

/-- `L₀₀ L₁₁ - L₀₁ L₁₀` evaluated at a complex vector, in monomial form. -/
theorem det_expand (A : Fin 2 → Fin 2 → Fin 3 → ℚ) (w : Fin 3 → ℂ) :
    (∑ k, (A 0 0 k : ℂ) * w k) * (∑ k, (A 1 1 k : ℂ) * w k)
      - (∑ k, (A 0 1 k : ℂ) * w k) * (∑ k, (A 1 0 k : ℂ) * w k)
      = (gco A 0 0 : ℂ) * w 0 ^ 2 + (gco A 1 1 : ℂ) * w 1 ^ 2 + (gco A 2 2 : ℂ) * w 2 ^ 2
        + ((gco A 0 1 + gco A 1 0 : ℚ) : ℂ) * (w 0 * w 1)
        + ((gco A 0 2 + gco A 2 0 : ℚ) : ℂ) * (w 0 * w 2)
        + ((gco A 1 2 + gco A 2 1 : ℚ) : ℂ) * (w 1 * w 2) := by
  simp only [Fin.sum_univ_three, gco]
  push_cast
  ring

/-- `L₀₀ L₁₁ - L₀₁ L₁₀` evaluated at a rational vector, in monomial form. -/
theorem det_expand_Q (A : Fin 2 → Fin 2 → Fin 3 → ℚ) (v : Fin 3 → ℚ) :
    (∑ k, A 0 0 k * v k) * (∑ k, A 1 1 k * v k) - (∑ k, A 0 1 k * v k) * (∑ k, A 1 0 k * v k)
      = gco A 0 0 * v 0 ^ 2 + gco A 1 1 * v 1 ^ 2 + gco A 2 2 * v 2 ^ 2
        + (gco A 0 1 + gco A 1 0) * (v 0 * v 1) + (gco A 0 2 + gco A 2 0) * (v 0 * v 2)
        + (gco A 1 2 + gco A 2 1) * (v 1 * v 2) := by
  simp only [Fin.sum_univ_three, gco]
  ring

/-- `det M = 0` is a quadratic relation among `u, conj u, π i`, with coefficients from `A`. -/
theorem det_rel (A : Fin 2 → Fin 2 → Fin 3 → ℚ) (u : ℂ) (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = ∑ k, (A i j k : ℂ) * ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k)
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0) :
    ((gco A 0 0 : ℚ) : ℂ) * u ^ 2 + ((gco A 1 1 : ℚ) : ℂ) * conj u ^ 2
      + ((gco A 2 2 : ℚ) : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I) ^ 2
      + ((gco A 0 1 + gco A 1 0 : ℚ) : ℂ) * (u * conj u)
      + ((gco A 0 2 + gco A 2 0 : ℚ) : ℂ) * (u * (((Real.pi : ℝ) : ℂ) * Complex.I))
      + ((gco A 1 2 + gco A 2 1 : ℚ) : ℂ) * (conj u * (((Real.pi : ℝ) : ℂ) * Complex.I)) = 0 := by
  have h := det_expand A ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I]
  rw [← hM 0 0, ← hM 1 1, ← hM 0 1, ← hM 1 0, hdet, sub_self] at h
  exact h.symm

/-- A `ℚ`-linear relation between the coefficient vectors of two linear forms in `w` gives the
same relation between the forms. -/
theorem forms_rel (w : Fin 3 → ℂ) (a b : Fin 3 → ℚ) (p q : ℚ)
    (hab : ∀ k, p * a k + q * b k = 0) :
    (p : ℂ) * ∑ k, (a k : ℂ) * w k + (q : ℂ) * ∑ k, (b k : ℂ) * w k = 0 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  have hC : ((p * a k + q * b k : ℚ) : ℂ) = 0 := by exact_mod_cast hab k
  push_cast at hC
  linear_combination w k * hC

end P14Rel3

open P14Rel3 in
/-- `F` gives `a = b`, `e = -f` and `s ρ = Q(y, π)` with `s = 2a + d ≠ 0` (anisotropy at
`(1, 1, 0)`); `det M = 0` gives a relation `G` of the same shape. Since `π` is transcendental and
`y ∉ ℚ π`, `s' F = s G`. An isotropic rational vector of `G` (it is a determinant of linear
forms) then forces `s' = 0` (anisotropy of `F`) and hence `G = 0`, i.e. `det L = 0` identically;
the rank-one lemma for `L` gives dependent rows or columns, transferred to `M`. -/
theorem solution (u : ℂ) (hre : u.re ≠ 0)
    (him : ∀ q : ℚ, u.im ≠ (q : ℝ) * Real.pi) (hρ : IsAlgebraic ℚ (u * conj u))
    (a b c d e f : ℚ)
    (hrel : (a : ℂ) * u ^ 2 + (b : ℂ) * conj u ^ 2 + (c : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I) ^ 2
        + (d : ℂ) * (u * conj u) + (e : ℂ) * (u * (((Real.pi : ℝ) : ℂ) * Complex.I))
        + (f : ℂ) * (conj u * (((Real.pi : ℝ) : ℂ) * Complex.I)) = 0)
    (hanis : ∀ v : Fin 3 → ℚ, a * v 0 ^ 2 + b * v 1 ^ 2 + c * v 2 ^ 2 + d * (v 0 * v 1)
        + e * (v 0 * v 2) + f * (v 1 * v 2) = 0 → v = 0)
    (A : Fin 2 → Fin 2 → Fin 3 → ℚ) (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = ∑ k, (A i j k : ℂ) * ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k)
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0) :
    (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ j, (p : ℂ) * M 0 j + (q : ℂ) * M 1 j = 0) ∨
      (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ i, (p : ℂ) * M i 0 + (q : ℂ) * M i 1 = 0) := by
  -- (1) the relation `F`: `a = b`, `e = -f`, `s ρ = 4a y² + 2e π y + c π²`, and `s ≠ 0`
  obtain ⟨hab, hef, hF⟩ :=
    (DiazModulus.conj_pair_quadratic_relation_iff u hre him a b c d e f).1 hrel
  have hs : 2 * a + d ≠ 0 := by
    intro h0
    have hv := hanis ![1, 1, 0] (by simp; linarith)
    have h00 := congr_fun hv 0
    simp at h00
  -- (2) the relation `G = det L`
  obtain ⟨hab', hef', hG⟩ :=
    (DiazModulus.conj_pair_quadratic_relation_iff u hre him (gco A 0 0) (gco A 1 1) (gco A 2 2)
      (gco A 0 1 + gco A 1 0) (gco A 0 2 + gco A 2 0) (gco A 1 2 + gco A 2 1)).1
      (det_rel A u M hM hdet)
  -- (3) `s' F = s G`
  have hρR : IsAlgebraic ℚ (u.re ^ 2 + u.im ^ 2) := norm_alg u hρ
  have hρ0 : u.re ^ 2 + u.im ^ 2 ≠ 0 := by positivity
  obtain ⟨R1, R5, R3⟩ := coeff_prop u.im _ him hρR hρ0 a c d e _ _ _ _ hs hF hG
  have R2 : (2 * gco A 0 0 + (gco A 0 1 + gco A 1 0)) * b = (2 * a + d) * gco A 1 1 := by
    linear_combination R1 - (2 * gco A 0 0 + (gco A 0 1 + gco A 1 0)) * hab + (2 * a + d) * hab'
  have R4 : (2 * gco A 0 0 + (gco A 0 1 + gco A 1 0)) * d
      = (2 * a + d) * (gco A 0 1 + gco A 1 0) := by
    linear_combination (-2 : ℚ) * R1
  have R6 : (2 * gco A 0 0 + (gco A 0 1 + gco A 1 0)) * f
      = (2 * a + d) * (gco A 1 2 + gco A 2 1) := by
    linear_combination -R5 + (2 * gco A 0 0 + (gco A 0 1 + gco A 1 0)) * hef - (2 * a + d) * hef'
  -- (4) an isotropic vector of `G` forces `s' = 0`, hence `G = 0`
  obtain ⟨v, hv0, hvdet⟩ := DiazModulus.det_linear_forms_isotropic A
  have hGv := det_expand_Q A v
  rw [hvdet, sub_self] at hGv
  have hFv : a * v 0 ^ 2 + b * v 1 ^ 2 + c * v 2 ^ 2 + d * (v 0 * v 1)
      + e * (v 0 * v 2) + f * (v 1 * v 2) ≠ 0 := fun h => hv0 (hanis v h)
  have hs' : 2 * gco A 0 0 + (gco A 0 1 + gco A 1 0) = 0 := by
    have h : (2 * gco A 0 0 + (gco A 0 1 + gco A 1 0)) * (a * v 0 ^ 2 + b * v 1 ^ 2 + c * v 2 ^ 2
        + d * (v 0 * v 1) + e * (v 0 * v 2) + f * (v 1 * v 2)) = 0 := by
      linear_combination v 0 ^ 2 * R1 + v 1 ^ 2 * R2 + v 2 ^ 2 * R3 + (v 0 * v 1) * R4
        + (v 0 * v 2) * R5 + (v 1 * v 2) * R6 - (2 * a + d) * hGv
    exact (mul_eq_zero.1 h).resolve_right hFv
  have key : ∀ t t' : ℚ, (2 * gco A 0 0 + (gco A 0 1 + gco A 1 0)) * t = (2 * a + d) * t' →
      t' = 0 := by
    intro t t' h
    rw [hs', zero_mul] at h
    exact (mul_eq_zero.1 h.symm).resolve_left hs
  have g00 := key _ _ R1
  have g11 := key _ _ R2
  have g22 := key _ _ R3
  have g01 := key _ _ R4
  have g02 := key _ _ R5
  have g12 := key _ _ R6
  -- (5) `det L = 0` identically: rank-one lemma, transferred to `M`
  have hsym : ∀ k l : Fin 3, gco A k l + gco A l k = 0 := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      linarith
  have hdet' : ∀ k l : Fin 3,
      A 0 0 k * A 1 1 l + A 0 0 l * A 1 1 k = A 0 1 k * A 1 0 l + A 0 1 l * A 1 0 k := by
    intro k l
    have h := hsym k l
    simp only [gco] at h
    linarith
  rcases DiazModulus.det_zero_linear_forms_rank_one 3 A hdet' with
    ⟨p, q, hpq, hrow⟩ | ⟨p, q, hpq, hcol⟩
  · left
    refine ⟨p, q, hpq, fun j => ?_⟩
    rw [hM 0 j, hM 1 j]
    exact forms_rel _ (A 0 j) (A 1 j) p q (fun k => hrow j k)
  · right
    refine ⟨p, q, hpq, fun i => ?_⟩
    rw [hM i 0, hM i 1]
    exact forms_rel _ (A i 0) (A i 1) p q (fun k => hcol i k)

#print axioms solution
