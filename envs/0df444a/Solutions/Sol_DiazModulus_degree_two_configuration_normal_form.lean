-- Prove2me | solution 1 for DiazModulus.degree_two_configuration_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:27:17.291625+00:00
-- url     : https://prove2.me/submissions/f3c2289f-f7bf-4eb3-8476-1c3836704d05

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_degree_two_configuration_multiplier_complement
import Theorems.Thm_DiazModulus_coprime_pencil_mobius
import Theorems.Thm_DiazModulus_quadratic_complement_eigen_forms
import Theorems.Thm_DiazModulus_quadratic_eigen_forms_canonical

open Complex ComplexConjugate

/-! # Theorem NF: the degree-two normal form

Put `h = p(u)/q(u)`. Since `x` is free, `x₀ ≠ 0`; and `q(u) ≠ 0`, for otherwise `x₁ q(u) = x₀ p(u)`
gives `p(u) = 0` as well, against `a p + b q = 1`. So `x₁ = x₀ h`, and `y' = x₀ y` is a free triple
(multiplication by `x₀ ≠ 0` is an injective `Q̄`-linear map) with `y' ⊆ W` and `h y' = x₁ y ⊆ W`.
`DiazModulus.degree_two_configuration_multiplier_complement` gives `λ ∈ {0, 1, 2}` and `g₁, g₂` with
`W = ⟨1, u, u⁻¹, g₁, g₂⟩` and `k g_j ∈ W` for `k = q(u)/(p(u) − λ q(u))`. The new pencil
`P = q`, `Q = p − λq` is coprime of maximal degree 2 by `DiazModulus.coprime_pencil_mobius` (determinant
`−1`), and `k = P(u)/Q(u)`. `DiazModulus.quadratic_complement_eigen_forms` applied to `g = (g₁, g₂)`
on `S = W` gives the scalar, two-orbit or cyclic eigen-forms, and
`DiazModulus.quadratic_eigen_forms_canonical` turns them into D1, D2a or D2b.
-/

namespace R20_nf

open DiazModulus Polynomial

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

end R20_nf

open DiazModulus R20_nf in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) (hxy : ∀ i j, x i * y j ∈ W)
    (p q : (↥Qbar)[X]) (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2)
    (hpq : x 1 * aeval u q = x 0 * aeval u p) :
    (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ W ∧ u * t j ∈ W) ∨ (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u P' * aeval u S₂ / (u * aeval u Q')} : Set ℂ)) ∨
    (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u Q' * (aeval u Q' * aeval u S₁ + aeval u P' * aeval u S₂) / (u * aeval u P' ^ 2)} :
            Set ℂ)) := by
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  have hq : aeval u q ≠ 0 := by
    intro hq0
    have hp0 : aeval u p = 0 := by
      have h' := hpq
      rw [hq0, mul_zero] at h'
      exact (mul_eq_zero.mp h'.symm).resolve_left hx0
    obtain ⟨a, b, hab⟩ := id hcop
    have h' := congrArg (aeval u) hab
    simp [hp0, hq0] at h'
  -- the triple `y' = x₀ y`
  have hy' : LinearIndependent (↥Qbar) (fun j => x 0 * y j) :=
    hy.map' (LinearMap.mulLeft (↥Qbar) (x 0)) (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hx0))
  have hyh : ∀ j, aeval u p / aeval u q * (x 0 * y j) ∈ W := fun j => by
    have e : aeval u p / aeval u q * (x 0 * y j) = x 1 * y j := by
      rw [div_mul_eq_mul_div, div_eq_iff hq]
      linear_combination (-(y j)) * hpq
    rw [e]; exact hxy 1 j
  obtain ⟨lam, -, g₁, g₂, hWeq, hg₁, hg₂⟩ :=
    DiazModulus.degree_two_configuration_multiplier_complement u hu W hW h1 hu1 hui p q hcop hdeg
      (fun j => x 0 * y j) hy' (fun j => hxy 0 j) hyh
  -- the new pencil `P = q`, `Q = p − λ q`
  obtain ⟨hcop', hdeg'⟩ := DiazModulus.coprime_pencil_mobius p q hcop hdeg 0 1 1 (-lam) (by simp)
  have hPu : aeval u (C 0 * p + C 1 * q) = aeval u q := by simp
  have hQu : aeval u (C 1 * p + C (-lam) * q) = aeval u p - (lam : ℂ) * aeval u q := by
    simp only [map_add, map_mul, aeval_C, am]; push_cast; ring
  have hS : Submodule.span Qbar ({1, u, u⁻¹, ![g₁, g₂] 0, ![g₁, g₂] 1} : Set ℂ) = W := by
    rw [hWeq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h5 : Module.finrank (↥Qbar)
      (Submodule.span Qbar ({1, u, u⁻¹, ![g₁, g₂] 0, ![g₁, g₂] 1} : Set ℂ)) = 5 := by
    rw [hS]; exact hW
  have hk : ∀ j, aeval u (C 0 * p + C 1 * q) / aeval u (C 1 * p + C (-lam) * q) * ![g₁, g₂] j ∈
      Submodule.span Qbar ({1, u, u⁻¹, ![g₁, g₂] 0, ![g₁, g₂] 1} : Set ℂ) := by
    intro j
    rw [hS, hPu, hQu]
    fin_cases j
    · exact hg₁
    · exact hg₂
  have hform := DiazModulus.quadratic_complement_eigen_forms u hu _ _ hcop' hdeg' ![g₁, g₂] h5 hk
  rw [hS] at hform
  exact DiazModulus.quadratic_eigen_forms_canonical u hu W hW h1 hu1 hui _ _ hcop' hdeg' hform
