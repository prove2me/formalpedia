-- Prove2me | solution 1 for DiazModulus.progression_space_contains_square_or_reciprocal_or_eq_involution_pencil_space
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T19:25:07.542457+00:00
-- url     : https://prove2.me/submissions/d5639c59-9594-4851-8de6-b38bd4d5fb13

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_progression_space_ratio_degree_le_two
import Theorems.Thm_DiazModulus_quadratic_ratio_progression_space_eq_involution_pencil_space
import Theorems.Thm_DiazModulus_mobius_progression_space_contains_square_or_reciprocal

open Complex ComplexConjugate

/-! # A progression space of dimension 5 contains `u²`, `u⁻²`, some `(u − b)⁻¹`, or is a pencil space

By `progression_space_ratio_degree_le_two`, `max (deg p, deg q) ≤ 2`. If the maximum is 2,
`quadratic_ratio_progression_space_eq_involution_pencil_space` gives the right disjunct. If it is 1,
write `p = αX + β`, `q = γX + δ`. Then `q(u) ≠ 0` and `h = p(u)/q(u) ∉ Q̄` (else `p = t q` and
coprimality makes both constant). If `αδ − βγ = 0`, then `γ h = α` and `δ h = β`, so `h ∈ Q̄` unless
`γ = δ = 0`, i.e. `q = 0`; hence `αδ − βγ ≠ 0`. Rewriting `h = (αu + β)/(γu + δ)` in the space and
in the goal, `mobius_progression_space_contains_square_or_reciprocal` gives the left disjunct.
-/

namespace R13_pencilI3

open DiazModulus Polynomial

theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem h_not_mem {u : ℂ} (hu : u ∉ Qbar) {p q : (↥Qbar)[X]} (hpq : IsCoprime p q)
    (hdeg : 1 ≤ max p.natDegree q.natDegree) (hq : aeval u q ≠ 0) :
    aeval u p / aeval u q ∉ Qbar := by
  intro ht
  have e : p = C (⟨_, ht⟩ : ↥Qbar) * q := by
    apply sub_eq_zero.1; apply aeval_eq_zero hu
    simp only [map_sub, map_mul, aeval_C, am]
    field_simp; ring
  rw [e] at hpq hdeg
  have hU : IsUnit q := isCoprime_self.1 (IsCoprime.mul_left_iff.1 hpq).2
  have h0 := natDegree_eq_zero_of_isUnit hU
  have h1 := natDegree_C_mul_le (⟨_, ht⟩ : ↥Qbar) q
  omega

theorem aeval_lin {p : (↥Qbar)[X]} (hp : p.natDegree ≤ 1) (u : ℂ) :
    aeval u p = (p.coeff 1 : ℂ) * u + p.coeff 0 := by
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hp]
  simp [am]

end R13_pencilI3

open DiazModulus R13_pencilI3 Polynomial in
theorem solution
    (u : ℂ) (hu : u ∉ Qbar) (p q : Polynomial ↥Qbar) (hcop : IsCoprime p q)
    (hdeg : 1 ≤ max p.natDegree q.natDegree) (c : ℂ) (hc : c ≠ 0)
    (hdim : Module.finrank (↥Qbar) (Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ)))) = 5) :
    (u ^ 2 ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ))) ∨
      (u ^ 2)⁻¹ ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ))) ∨
      ∃ b ∈ Qbar, b ≠ 0 ∧ (u - b)⁻¹ ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ)))) ∨
    ∃ l₁ l₂ : Polynomial ↥Qbar,
      l₁ ∈ Submodule.span ↥Qbar ({p, q} : Set (Polynomial ↥Qbar)) ∧ l₁ ≠ 0 ∧
      l₂ ∈ Submodule.span ↥Qbar ({p, q} : Set (Polynomial ↥Qbar)) ∧ l₂ ≠ 0 ∧
      Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ))) =
        Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
          Polynomial.aeval u p ^ (i : ℕ) * Polynomial.aeval u q ^ (3 - (i : ℕ)) /
            (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂))) := by
  have hle := DiazModulus.progression_space_ratio_degree_le_two u hu p q hcop hdeg c hc hdim
  rcases (by omega : max p.natDegree q.natDegree = 2 ∨ max p.natDegree q.natDegree ≤ 1) with h2 | h1
  · exact Or.inr (DiazModulus.quadratic_ratio_progression_space_eq_involution_pencil_space
      u hu p q hcop h2 c hc hdim)
  left
  have hp1 : p.natDegree ≤ 1 := le_trans (le_max_left _ _) h1
  have hq1 : q.natDegree ≤ 1 := le_trans (le_max_right _ _) h1
  have hq0 : q ≠ 0 := by
    intro e
    rw [e] at hcop hdeg
    have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop)
    rw [natDegree_zero, max_eq_left (Nat.zero_le _)] at hdeg; omega
  have hqu : aeval u q ≠ 0 := fun e => hq0 (aeval_eq_zero hu e)
  have hh := h_not_mem hu hcop hdeg hqu
  have ep := aeval_lin hp1 u
  have eq := aeval_lin hq1 u
  have hdet : (p.coeff 1 : ℂ) * q.coeff 0 - p.coeff 0 * q.coeff 1 ≠ 0 := by
    intro hd
    by_cases hγ : (q.coeff 1 : ℂ) = 0
    · by_cases hδ : (q.coeff 0 : ℂ) = 0
      · exact hqu (by rw [eq, hγ, hδ]; ring)
      · apply hh
        have : aeval u p / aeval u q = (p.coeff 0 : ℂ) / q.coeff 0 := by
          rw [div_eq_div_iff hqu hδ, ep, eq]; linear_combination u * hd
        rw [this]; exact div_mem (p.coeff 0).2 (q.coeff 0).2
    · apply hh
      have : aeval u p / aeval u q = (p.coeff 1 : ℂ) / q.coeff 1 := by
        rw [div_eq_div_iff hqu hγ, ep, eq]; linear_combination -hd
      rw [this]; exact div_mem (p.coeff 1).2 (q.coeff 1).2
  have e : aeval u p / aeval u q =
      ((p.coeff 1 : ℂ) * u + p.coeff 0) / ((q.coeff 1 : ℂ) * u + q.coeff 0) := by rw [ep, eq]
  rw [e] at hdim ⊢
  exact DiazModulus.mobius_progression_space_contains_square_or_reciprocal u hu _ _ _ _ c
    (p.coeff 1).2 (p.coeff 0).2 (q.coeff 1).2 (q.coeff 0).2 hdet hc hdim
