-- Prove2me | solution 2 for DiazModulus.generic_qbar_homogeneous_four_exp_barrier
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:19:03.864412+00:00
-- url     : https://prove2.me/submissions/23bf313e-e34e-4128-a815-d0c2dfb8683e

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_qbar_dependent_of_det_linear_forms
import Theorems.Thm_DiazModulus_generic_quadratic_relation_is_norm

open Complex ComplexConjugate

namespace P15Hom

/-- The three generators as a range. -/
theorem range3 (a b c : ℂ) : Set.range ![a, b, c] = ({a, b, c} : Set ℂ) := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- Algebraic coefficients of an element of the `Q̄`-span of `u, conj u, πi`, written in the four
coordinates `1, u, conj u, πi` with a zero constant coefficient. -/
theorem coeffs3 (u z : ℂ)
    (h : z ∈ Submodule.span DiazModulus.Qbar
      ({u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ)) :
    ∃ C : Fin 4 → ℂ, (∀ k, IsAlgebraic ℚ (C k)) ∧ C 0 = 0 ∧
      z = ∑ k, C k * ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k := by
  rw [← range3, Submodule.mem_span_range_iff_exists_fun] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨![0, (c 0 : ℂ), (c 1 : ℂ), (c 2 : ℂ)], ?_, rfl, ?_⟩
  · intro k
    fin_cases k
    · exact isAlgebraic_zero
    · exact DiazModulus.mem_Qbar_iff.1 (c 0).2
    · exact DiazModulus.mem_Qbar_iff.1 (c 1).2
    · exact DiazModulus.mem_Qbar_iff.1 (c 2).2
  · rw [← hc]
    have hs : ∑ k, c k • ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k
        = ∑ k, (c k : ℂ) * ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k := rfl
    rw [hs]
    simp [Fin.sum_univ_three, Fin.sum_univ_four]

/-- Two vectors, independent over `Q̄`. -/
theorem li2 {x : Fin 2 → ℂ} (hx : LinearIndependent (↥DiazModulus.Qbar) x)
    (p q : ↥DiazModulus.Qbar) (h : (p : ℂ) * x 0 + (q : ℂ) * x 1 = 0) : p = 0 ∧ q = 0 := by
  have := Fintype.linearIndependent_iff.1 hx ![p, q] (by
    simp only [Fin.sum_univ_two]
    exact h)
  exact ⟨by simpa using this 0, by simpa using this 1⟩

/-- `generic_quadratic_relation_is_norm` applied to the difference of two products of linear forms
    in `1, u, conj u, πi`. -/
theorem det_norm (u : ℂ) (hu : u ≠ 0) (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥DiazModulus.Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (a b c d : Fin 4 → ℂ) (ha : ∀ k, IsAlgebraic ℚ (a k)) (hb : ∀ k, IsAlgebraic ℚ (b k))
    (hc : ∀ k, IsAlgebraic ℚ (c k)) (hd : ∀ k, IsAlgebraic ℚ (d k))
    (hrel : (∑ k, a k * ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k)
        * (∑ k, b k * ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k)
      = (∑ k, c k * ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k)
        * (∑ k, d k * ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k)) :
    ∃ γ : ℂ, IsAlgebraic ℚ γ ∧ ∀ z : Fin 4 → ℂ,
      (∑ k, a k * z k) * (∑ k, b k * z k) - (∑ k, c k * z k) * (∑ k, d k * z k)
        = γ * (z 1 * z 2 - u * conj u * z 0 ^ 2) := by
  have hsum : ∀ z : Fin 4 → ℂ, ∑ k, ∑ l, (a k * b l - c k * d l) * z k * z l
      = (∑ k, a k * z k) * (∑ k, b k * z k) - (∑ k, c k * z k) * (∑ k, d k * z k) := by
    intro z
    simp only [Fin.sum_univ_four]
    ring
  obtain ⟨γ, hγ, hQ⟩ := DiazModulus.generic_quadratic_relation_is_norm u hu hρ hgen
    (fun k l => a k * b l - c k * d l) (fun k l => ((ha k).mul (hb l)).sub ((hc k).mul (hd l)))
    (by rw [hsum, hrel, sub_self])
  exact ⟨γ, hγ, fun z => by rw [← hsum z]; exact hQ z⟩

end P15Hom

/- Write each product in the four coordinates `1, u, conj u, πi`, with zero constant coefficient.
The determinant relation `x₀y₀ · x₁y₁ = x₀y₁ · x₁y₀` is a quadratic relation among these numbers, so
by `generic_quadratic_relation_is_norm` its quadratic form is `c · (z₁z₂ - ρ z₀²)`; at `z = (1, 0, 0, 0)` the form vanishes (no
constant coefficients) while the norm is `-ρ ≠ 0`, so `c = 0`. The determinant then vanishes
identically; `qbar_dependent_of_det_linear_forms` gives an algebraic row or column relation, and since `y₀ ≠ 0` and
`x₀ ≠ 0` this is an algebraic relation between `x₀, x₁` or between `y₀, y₁`. -/
open P15Hom DiazModulus in
theorem solution (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (x y : Fin 2 → ℂ) (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y) :
    ¬ ∀ i j, x i * y j ∈ Submodule.span Qbar ({u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ) := by
  intro hmem
  have hex := fun i j => coeffs3 u (x i * y j) (hmem i j)
  choose C hC hC0 hCe using hex
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  have hy0 : y 0 ≠ 0 := hy.ne_zero 0
  obtain ⟨γ, -, hQ⟩ := det_norm u hu hρ hgen (C 0 0) (C 1 1) (C 0 1) (C 1 0)
    (hC 0 0) (hC 1 1) (hC 0 1) (hC 1 0)
    (by rw [← hCe 0 0, ← hCe 1 1, ← hCe 0 1, ← hCe 1 0]; ring)
  -- at `z = (1, 0, 0, 0)` the form vanishes and the norm is `-u * conj u`
  have hγ : γ = 0 := by
    have h := hQ ![1, 0, 0, 0]
    simp [Fin.sum_univ_four, hC0] at h
    exact h.resolve_right hu
  rcases DiazModulus.qbar_dependent_of_det_linear_forms
    ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] C hC x y 0 1 hx0 hy0 hCe
    (fun z => by rw [hQ z, hγ, zero_mul]) with ⟨p, q, hpq, h⟩ | ⟨p, q, hpq, h⟩
  · exact hpq (li2 hx p q h)
  · exact hpq (li2 hy p q h)

#print axioms solution
