-- Prove2me | solution 2 for DiazModulus.generic_no_strong_six_exp_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:19:01.272989+00:00
-- url     : https://prove2.me/submissions/3b512588-b2f1-411e-baa8-c878f7b78adc

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_qbar_dependent_of_det_linear_forms
import Theorems.Thm_DiazModulus_generic_quadratic_relation_is_norm

open Complex ComplexConjugate

namespace P15Six

/-- The four generators as a range. -/
theorem range4 (a b c d : ℂ) : Set.range ![a, b, c, d] = ({a, b, c, d} : Set ℂ) := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

/-- Algebraic coefficients of an element of the `Q̄`-span of `1, u, conj u, πi`. -/
theorem coeffs (u z : ℂ)
    (h : z ∈ Submodule.span DiazModulus.Qbar
      ({1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ)) :
    ∃ C : Fin 4 → ℂ, (∀ k, IsAlgebraic ℚ (C k)) ∧
      z = ∑ k, C k * ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k := by
  rw [← range4, Submodule.mem_span_range_iff_exists_fun] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨fun k => (c k : ℂ), fun k => DiazModulus.mem_Qbar_iff.1 (c k).2, ?_⟩
  rw [← hc]
  rfl

/-- Two vectors, independent over `Q̄`. -/
theorem li2 {x : Fin 2 → ℂ} (hx : LinearIndependent (↥DiazModulus.Qbar) x)
    (p q : ↥DiazModulus.Qbar) (h : (p : ℂ) * x 0 + (q : ℂ) * x 1 = 0) : p = 0 ∧ q = 0 := by
  have := Fintype.linearIndependent_iff.1 hx ![p, q] (by
    simp only [Fin.sum_univ_two]
    exact h)
  exact ⟨by simpa using this 0, by simpa using this 1⟩

/-- Three vectors, independent over `Q̄`. -/
theorem li3 {y : Fin 3 → ℂ} (hy : LinearIndependent (↥DiazModulus.Qbar) y)
    (p q r : ↥DiazModulus.Qbar) (h : (p : ℂ) * y 0 + (q : ℂ) * y 1 + (r : ℂ) * y 2 = 0) :
    p = 0 ∧ q = 0 ∧ r = 0 := by
  have := Fintype.linearIndependent_iff.1 hy ![p, q, r] (by
    simp only [Fin.sum_univ_three]
    exact h)
  exact ⟨by simpa using this 0, by simpa using this 1, by simpa using this 2⟩

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

/-- A linear form evaluated at an explicit vector. -/
theorem sum4 (a : Fin 4 → ℂ) (z0 z1 z2 z3 : ℂ) :
    ∑ k, a k * ![z0, z1, z2, z3] k = a 0 * z0 + a 1 * z1 + a 2 * z2 + a 3 * z3 := by
  simp [Fin.sum_univ_four]

end P15Six

/- Write each product as `L i j (e)` with `L i j (z) = Σ C i j k z k` and `e = (1, u, conj u, πi)`.
(1) For each pair of columns `j < l` the minor `x₀y_j · x₁y_l - x₀y_l · x₁y_j` vanishes, a quadratic
relation among `1, u, conj u, πi`; by `generic_quadratic_relation_is_norm`, `L0j L1l - L0l L1j = c_jl · N` identically, with
`N(z) = z₁z₂ - ρ z₀²`.
(2) If `c₀₁ = 0`, the block of columns `0, 1` has identically vanishing determinant;
`qbar_dependent_of_det_linear_forms` gives an algebraic row relation (so `x₀, x₁` are dependent, as `y₀ ≠ 0`) or column relation (so
`y₀, y₁` are dependent, as `x₀ ≠ 0`).
(3) If `c₀₁ ≠ 0`, the Cramer identity `D₀ L₀₀ - D₁ L₀₁ + D₂ L₀₂ = 0` for the three minors reads
`N · Λ = 0` with `Λ = c₁₂ L₀₀ - c₀₂ L₀₁ + c₀₁ L₀₂`. Evaluating at four points where `N ≠ 0` kills
the coefficients of `Λ`; at `e` this gives `x₀ (c₁₂ y₀ - c₀₂ y₁ + c₀₁ y₂) = 0`, an algebraic
relation among the `y`'s with `c₀₁ ≠ 0`. -/
open P15Six DiazModulus in
theorem solution (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) :
    ¬ ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ) := by
  intro hmem
  have hex := fun i j => coeffs u (x i * y j) (hmem i j)
  choose C hC hCe using hex
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  have hy0 : y 0 ≠ 0 := hy.ne_zero 0
  -- (1) the three `2 × 2` minors are multiples of the norm form
  have hminor : ∀ j l : Fin 3, ∃ γ : ℂ, IsAlgebraic ℚ γ ∧ ∀ z : Fin 4 → ℂ,
      (∑ k, C 0 j k * z k) * (∑ k, C 1 l k * z k) - (∑ k, C 0 l k * z k) * (∑ k, C 1 j k * z k)
        = γ * (z 1 * z 2 - u * conj u * z 0 ^ 2) := fun j l =>
    det_norm u hu hρ hgen (C 0 j) (C 1 l) (C 0 l) (C 1 j) (hC 0 j) (hC 1 l) (hC 0 l) (hC 1 j)
      (by rw [← hCe 0 j, ← hCe 1 l, ← hCe 0 l, ← hCe 1 j]; ring)
  obtain ⟨c01, hc01, E01⟩ := hminor 0 1
  obtain ⟨c02, hc02, E02⟩ := hminor 0 2
  obtain ⟨c12, hc12, E12⟩ := hminor 1 2
  by_cases h01 : c01 = 0
  · -- (2) the block of columns `0, 1` has identically vanishing determinant
    rcases DiazModulus.qbar_dependent_of_det_linear_forms
      ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] C hC x y 0 1 hx0 hy0 hCe
      (fun z => by rw [E01 z, h01, zero_mul]) with ⟨p, q, hpq, h⟩ | ⟨p, q, hpq, h⟩
    · exact hpq (li2 hx p q h)
    · obtain ⟨hp, hq, -⟩ := li3 hy p q 0 (by simpa using h)
      exact hpq ⟨hp, hq⟩
  · -- (3) Cramer: `N · Λ = 0` identically
    have hN : ∀ z : Fin 4 → ℂ, (z 1 * z 2 - u * conj u * z 0 ^ 2) *
        (c12 * (∑ k, C 0 0 k * z k) - c02 * (∑ k, C 0 1 k * z k)
          + c01 * (∑ k, C 0 2 k * z k)) = 0 := by
      intro z
      linear_combination (-(∑ k, C 0 0 k * z k)) * E12 z + (∑ k, C 0 1 k * z k) * E02 z
        - (∑ k, C 0 2 k * z k) * E01 z
    have key : ∀ z : Fin 4 → ℂ, z 1 * z 2 - u * conj u * z 0 ^ 2 ≠ 0 →
        c12 * (∑ k, C 0 0 k * z k) - c02 * (∑ k, C 0 1 k * z k)
          + c01 * (∑ k, C 0 2 k * z k) = 0 :=
      fun z hz => (mul_eq_zero.1 (hN z)).resolve_left hz
    -- four points where the norm form is `1, 2, 1, 1`
    have h1 := key ![0, 1, 1, 0] (by simp)
    have h2 := key ![0, 1, 2, 0] (by simp)
    have h3 := key ![0, 1, 1, 1] (by simp)
    have h4 := key ![1, 1, 1 + u * conj u, 0] (by simp)
    rw [sum4, sum4, sum4] at h1 h2 h3 h4
    have e0 := hCe 0 0
    have e1 := hCe 0 1
    have e2 := hCe 0 2
    rw [sum4] at e0 e1 e2
    have hfin : x 0 * (c12 * y 0 - c02 * y 1 + c01 * y 2) = 0 := by
      linear_combination c12 * e0 - c02 * e1 + c01 * e2
        + (h4 - h1 - (u * conj u) * (h2 - h1)) + u * (2 * h1 - h2) + conj u * (h2 - h1)
        + (((Real.pi : ℝ) : ℂ) * Complex.I) * (h3 - h1)
    have hne : c12 * y 0 - c02 * y 1 + c01 * y 2 = 0 := (mul_eq_zero.1 hfin).resolve_left hx0
    obtain ⟨-, -, hr⟩ := li3 hy ⟨c12, DiazModulus.mem_Qbar_iff.2 hc12⟩
      ⟨-c02, DiazModulus.mem_Qbar_iff.2 hc02.neg⟩ ⟨c01, DiazModulus.mem_Qbar_iff.2 hc01⟩ (by
        show c12 * y 0 + -c02 * y 1 + c01 * y 2 = 0
        linear_combination hne)
    exact h01 (by simpa using congrArg Subtype.val hr)

#print axioms solution
