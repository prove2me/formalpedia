-- Prove2me | solution 1 for DiazModulus.generic_qbar_homogeneous_four_exp_barrier
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T07:01:39.532983+00:00
-- url     : https://prove2.me/submissions/4577b62b-fb53-4274-92d9-a01873d730be

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_det_zero_linear_forms_rank_one_field
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

/-- Polarisation of a vanishing difference of products of linear forms. -/
theorem polar2 (a b c d : Fin 4 → ℂ)
    (h : ∀ z : Fin 4 → ℂ,
      (∑ k, a k * z k) * (∑ k, b k * z k) - (∑ k, c k * z k) * (∑ k, d k * z k) = 0)
    (k l : Fin 4) : a k * b l + a l * b k = c k * d l + c l * d k := by
  have h1 := h (Pi.single k 1 + Pi.single l 1)
  have h2 := h (Pi.single k 1)
  have h3 := h (Pi.single l 1)
  simp [Pi.single_apply, mul_add, Finset.sum_add_distrib] at h1 h2 h3
  linear_combination h1 - h2 - h3

/-- `N6` applied to the difference of two products of linear forms in `1, u, conj u, πi`. -/
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

/-- A `2 × 2` block of products `x i * y j` whose determinant vanishes identically as a quadratic
form: by `N5` over `Q̄`, the rows or the columns satisfy an algebraic linear relation. -/
theorem block {m : ℕ} (e : Fin 4 → ℂ) (C : Fin 2 → Fin m → Fin 4 → ℂ)
    (hC : ∀ i j k, IsAlgebraic ℚ (C i j k)) (x : Fin 2 → ℂ) (y : Fin m → ℂ) (j0 j1 : Fin m)
    (hx0 : x 0 ≠ 0) (hy0 : y j0 ≠ 0)
    (hxy : ∀ i j, x i * y j = ∑ k, C i j k * e k)
    (hdet : ∀ z : Fin 4 → ℂ, (∑ k, C 0 j0 k * z k) * (∑ k, C 1 j1 k * z k)
      - (∑ k, C 0 j1 k * z k) * (∑ k, C 1 j0 k * z k) = 0) :
    (∃ p q : ↥DiazModulus.Qbar, ¬(p = 0 ∧ q = 0) ∧ (p : ℂ) * x 0 + (q : ℂ) * x 1 = 0) ∨
      (∃ p q : ↥DiazModulus.Qbar, ¬(p = 0 ∧ q = 0) ∧ (p : ℂ) * y j0 + (q : ℂ) * y j1 = 0) := by
  have hpol := polar2 (C 0 j0) (C 1 j1) (C 0 j1) (C 1 j0) hdet
  let A : Fin 2 → Fin 2 → Fin 4 → ↥DiazModulus.Qbar :=
    fun i j k => ⟨C i (![j0, j1] j) k, DiazModulus.mem_Qbar_iff.2 (hC _ _ _)⟩
  have hA : ∀ i j k, ((A i j k : ↥DiazModulus.Qbar) : ℂ) = C i (![j0, j1] j) k :=
    fun _ _ _ => rfl
  have hdetA : ∀ k l : Fin 4,
      A 0 0 k * A 1 1 l + A 0 0 l * A 1 1 k = A 0 1 k * A 1 0 l + A 0 1 l * A 1 0 k := by
    intro k l
    apply Subtype.ext
    simp only [Subfield.coe_add, Subfield.coe_mul, hA, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hpol k l
  rcases DiazModulus.det_zero_linear_forms_rank_one_field 4 A hdetA with
    ⟨p, q, hpq, hr⟩ | ⟨p, q, hpq, hr⟩
  · left
    refine ⟨p, q, hpq, ?_⟩
    have hr' : ∀ k, (p : ℂ) * C 0 j0 k + (q : ℂ) * C 1 j0 k = 0 := by
      intro k
      have := congrArg Subtype.val (hr 0 k)
      simpa [hA] using this
    have e1 := hxy 0 j0
    have e2 := hxy 1 j0
    simp only [Fin.sum_univ_four] at e1 e2
    have h : ((p : ℂ) * x 0 + (q : ℂ) * x 1) * y j0 = 0 := by
      linear_combination (p : ℂ) * e1 + (q : ℂ) * e2 + e 0 * hr' 0 + e 1 * hr' 1
        + e 2 * hr' 2 + e 3 * hr' 3
    exact (mul_eq_zero.1 h).resolve_right hy0
  · right
    refine ⟨p, q, hpq, ?_⟩
    have hr' : ∀ k, (p : ℂ) * C 0 j0 k + (q : ℂ) * C 0 j1 k = 0 := by
      intro k
      have := congrArg Subtype.val (hr 0 k)
      simpa [hA] using this
    have e1 := hxy 0 j0
    have e2 := hxy 0 j1
    simp only [Fin.sum_univ_four] at e1 e2
    have h : x 0 * ((p : ℂ) * y j0 + (q : ℂ) * y j1) = 0 := by
      linear_combination (p : ℂ) * e1 + (q : ℂ) * e2 + e 0 * hr' 0 + e 1 * hr' 1
        + e 2 * hr' 2 + e 3 * hr' 3
    exact (mul_eq_zero.1 h).resolve_left hx0

end P15Hom

open P15Hom in
/-- Write each product in the four coordinates `1, u, conj u, πi`, with zero constant coefficient.
The determinant relation `x₀y₀ · x₁y₁ = x₀y₁ · x₁y₀` is a quadratic relation among these numbers, so
by `N6` its quadratic form is `c · (z₁z₂ - ρ z₀²)`; at `z = (1, 0, 0, 0)` the form vanishes (no
constant coefficients) while the norm is `-ρ ≠ 0`, so `c = 0`. The determinant then vanishes
identically; `N5` over `Q̄` gives an algebraic row or column relation, and since `y₀ ≠ 0` and
`x₀ ≠ 0` this is an algebraic relation between `x₀, x₁` or between `y₀, y₁`. -/
theorem solution (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥DiazModulus.Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (x y : Fin 2 → ℂ) (hx : LinearIndependent (↥DiazModulus.Qbar) x) (hy : LinearIndependent (↥DiazModulus.Qbar) y) :
    ¬ ∀ i j, x i * y j ∈ Submodule.span DiazModulus.Qbar ({u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ) := by
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
  rcases block ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] C hC x y 0 1 hx0 hy0 hCe
    (fun z => by rw [hQ z, hγ, zero_mul]) with ⟨p, q, hpq, h⟩ | ⟨p, q, hpq, h⟩
  · exact hpq (li2 hx p q h)
  · exact hpq (li2 hy p q h)

#print axioms solution
