-- Prove2me | solution 1 for DiazModulus.rational_degree_one_space_visible_to_four_dimensional_extensions_iff_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T09:47:58.065739+00:00
-- url     : https://prove2.me/submissions/3f5a5786-4fbc-45b7-80af-c47edc74b930

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_degree_one_space_visible_to_four_dimensional_extensions_iff_cubic_over_quadratic
import Theorems.Thm_DiazModulus_coprime_fraction_cubic_over_quadratic_iff_natDegree_le

open Complex ComplexConjugate

/-! # Rational degree-one spaces: the visibility criterion by degrees

Let `u ∉ Q̄` with `u ū` algebraic, and `g = P(u)/Q(u)` with `P, Q ∈ Q̄[X]` coprime, such that
`1, u, ū, g, ug` are `Q̄`-free.

* `Q ≠ 0`: otherwise `Q(u) = 0`, so `g = 0`, against the freeness.
* By `degree_one_space_visible_to_four_dimensional_extensions_iff_cubic_over_quadratic`, the space
  is visible exactly when `u R(u) g = N(u)` for some `R ≠ 0`, `deg R ≤ 2`, `deg N ≤ 3`.
* `u` is transcendental over `Q̄`, so `aeval u` is injective and `Q(u) ≠ 0`. Hence
  `u R(u) P(u)/Q(u) = N(u)` holds exactly when `X·R·P = N·Q` in `Q̄[X]`.
* `coprime_fraction_cubic_over_quadratic_iff_natDegree_le` turns this into
  `max(deg P, deg Q) ≤ 2`, or `Q(0) = 0` and `max(deg P, deg Q) ≤ 3`; splitting on `Q(0) = 0`,
  that is the single bound `max(deg P, deg Q) ≤ 2 + [Q(0) = 0]`.
-/

namespace R17_vis2

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem aeval_injective {u : ℂ} (hu : u ∉ Qbar) :
    Function.Injective (aeval (R := ↥Qbar) u) :=
  (injective_iff_map_eq_zero _).2 fun P hP => transcendental_iff.1 (tr_of_not_mem hu) P hP

/-- Clearing the denominator `Q(u)`. -/
theorem eq_iff {u : ℂ} (hu : u ∉ Qbar) {P Q R N : (↥Qbar)[X]} (hQ : Q ≠ 0) :
    u * aeval u R * (aeval u P / aeval u Q) = aeval u N ↔ X * R * P = N * Q := by
  have hQu : aeval u Q ≠ 0 := fun h =>
    hQ (aeval_injective hu (by rw [h, map_zero]))
  rw [mul_div_assoc', div_eq_iff hQu, ← (aeval_injective hu).eq_iff]
  simp only [map_mul, aeval_X]

/-- The disjunction of the coprime-fraction leaf as one inequality. -/
theorem disj_iff (p q : ℕ) (hc : Prop) [Decidable hc] :
    (max p q ≤ 2 ∨ (hc ∧ max p q ≤ 3)) ↔ max p q ≤ 2 + (if hc then 1 else 0) := by
  split_ifs with h
  · simp only [h, true_and]
    omega
  · simp only [h, false_and, or_false, add_zero]

end R17_vis2

open DiazModulus R17_vis2 Polynomial in
theorem solution
    (u : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (P Q : (↥Qbar)[X]) (hcop : IsCoprime P Q)
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, aeval u P / aeval u Q, u * (aeval u P / aeval u Q)]) :
    (∃ w ∈ Submodule.span Qbar ({1, u, conj u, aeval u P / aeval u Q, u * (aeval u P / aeval u Q)} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) ∧
        ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ)) ↔
      max P.natDegree Q.natDegree ≤ 2 + (if Q.coeff 0 = 0 then 1 else 0) := by
  have hQ : Q ≠ 0 := by
    rintro rfl
    exact hind.ne_zero 3 (by simp)
  rw [DiazModulus.degree_one_space_visible_to_four_dimensional_extensions_iff_cubic_over_quadratic
    u _ hu hρ hind]
  have h1 : (∃ R N : (↥Qbar)[X], R ≠ 0 ∧ R.natDegree ≤ 2 ∧ N.natDegree ≤ 3 ∧
      u * aeval u R * (aeval u P / aeval u Q) = aeval u N) ↔
      ∃ R N : (↥Qbar)[X], R ≠ 0 ∧ R.natDegree ≤ 2 ∧ N.natDegree ≤ 3 ∧ X * R * P = N * Q := by
    simp only [eq_iff hu hQ]
  rw [h1, DiazModulus.coprime_fraction_cubic_over_quadratic_iff_natDegree_le (↥Qbar) P Q hcop hQ]
  exact disj_iff _ _ _
