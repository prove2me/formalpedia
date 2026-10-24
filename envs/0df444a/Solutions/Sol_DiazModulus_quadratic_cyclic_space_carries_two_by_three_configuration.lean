-- Prove2me | solution 1 for DiazModulus.quadratic_cyclic_space_carries_two_by_three_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:27:22.457441+00:00
-- url     : https://prove2.me/submissions/9bd8f068-e65a-4711-90b4-d90122eabe5a

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The cyclic space carries a 2 × 3 configuration

Write `H₀ = ⟨1, u, u⁻¹⟩`, `g₁ = Q R₁/(uP)`, `g₂ = Q(Q R₁ + P R₂)/(uP²)` (values at `u`). Since the span
of the five generators has dimension 5, the family `1, u, u⁻¹, g₁, g₂` is free
(`linearIndependent_iff_card_eq_finrank_span`); in particular `g₁ ≠ 0`, so `P(u), Q(u) ≠ 0`.
Every `R(u)/u` with `deg R ≤ 2` lies in `H₀` (`aeval_eq_sum_range'`), so a relation
`R(u)/u + a g₁ + b g₂ = 0` forces `a = b = 0` and `R(u) = 0`. The products are explicit:
`(P/Q)(Q/u) = P/u`, `(P/Q) g₁ = R₁/u` and `(P/Q) g₂ = g₁ + R₂/u`, while the row `1` gives
`Q/u, g₁, g₂`. Independence of `x = (1, P/Q)`: multiplying `a + b P/Q = 0` by `g₂` gives
`b R₂/u + b g₁ + a g₂ = 0`, so `a = b = 0`. Independence of `y = (Q/u, g₁, g₂)`: a relation reads
`a Q(u)/u + b g₁ + c g₂ = 0`, so `b = c = 0` and `a Q(u) = 0`, whence `a = 0`.
No transcendence is needed beyond `u ≠ 0`.
-/

namespace R20_cyclic

open DiazModulus Polynomial

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem indep5 {a b c d e : ℂ}
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({a, b, c, d, e} : Set ℂ)) = 5) :
    LinearIndependent (↥Qbar) ![a, b, c, d, e] := by
  have hr : Set.range ![a, b, c, d, e] = {a, b, c, d, e} := by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hr, h5, Fintype.card_fin]

theorem div_u {u : ℂ} (hu0 : u ≠ 0) {R : (↥Qbar)[X]} (hR : R.natDegree ≤ 2) :
    aeval u R / u = (R.coeff 1 : ℂ) * 1 + (R.coeff 2 : ℂ) * u + (R.coeff 0 : ℂ) * u⁻¹ := by
  rw [aeval_eq_sum_range' (n := 3) (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Subfield.smul_def, smul_eq_mul]
  field_simp
  ring

theorem cmul_mem {S : Submodule (↥Qbar) ℂ} (c : ↥Qbar) {v : ℂ} (hv : v ∈ S) : (c : ℂ) * v ∈ S := by
  simpa [Subfield.smul_def] using S.smul_mem c hv

theorem mem_div_u {u g₁ g₂ : ℂ} (hu0 : u ≠ 0) {R : (↥Qbar)[X]} (hR : R.natDegree ≤ 2) :
    aeval u R / u ∈ Submodule.span Qbar ({1, u, u⁻¹, g₁, g₂} : Set ℂ) := by
  rw [div_u hu0 hR]
  refine add_mem (add_mem (cmul_mem _ ?_) (cmul_mem _ ?_)) (cmul_mem _ ?_) <;>
    exact Submodule.subset_span (by simp)

/-- A relation `R(u)/u + a g₁ + b g₂ = 0` is trivial. -/
theorem mod_H0 {u g₁ g₂ : ℂ} (hu0 : u ≠ 0) (hL : LinearIndependent (↥Qbar) ![1, u, u⁻¹, g₁, g₂])
    {R : (↥Qbar)[X]} (hR : R.natDegree ≤ 2) (a b : ↥Qbar)
    (h : aeval u R / u + (a : ℂ) * g₁ + (b : ℂ) * g₂ = 0) : a = 0 ∧ b = 0 ∧ aeval u R = 0 := by
  have hc := Fintype.linearIndependent_iff.1 hL ![R.coeff 1, R.coeff 2, R.coeff 0, a, b] (by
    rw [div_u hu0 hR] at h
    simpa [Fin.sum_univ_five, Subfield.smul_def, add_assoc] using h)
  have ha : a = 0 := by simpa using hc 3
  have hb : b = 0 := by simpa using hc 4
  refine ⟨ha, hb, ?_⟩
  rw [ha, hb] at h
  simpa [hu0] using h

end R20_cyclic

open DiazModulus R20_cyclic in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar)
    (P Q R₁ R₂ : (↥Qbar)[X]) (hdeg : max P.natDegree Q.natDegree = 2)
    (hR₁ : R₁.natDegree ≤ 2) (hR₂ : R₂.natDegree ≤ 2)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u R₁ + aeval u P * aeval u R₂) / (u * aeval u P ^ 2)} : Set ℂ)) = 5) :
    LinearIndependent (↥Qbar) ![1, aeval u P / aeval u Q] ∧
    LinearIndependent (↥Qbar) ![aeval u Q / u, aeval u Q * aeval u R₁ / (u * aeval u P),
      aeval u Q * (aeval u Q * aeval u R₁ + aeval u P * aeval u R₂) / (u * aeval u P ^ 2)] ∧
    ∀ i j, ![1, aeval u P / aeval u Q] i *
      ![aeval u Q / u, aeval u Q * aeval u R₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u R₁ + aeval u P * aeval u R₂) / (u * aeval u P ^ 2)] j ∈
      Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u R₁ + aeval u P * aeval u R₂) / (u * aeval u P ^ 2)} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  have hL := indep5 h5
  have hP2 : P.natDegree ≤ 2 := hdeg ▸ le_max_left _ _
  have hQ2 : Q.natDegree ≤ 2 := hdeg ▸ le_max_right _ _
  have hPu : aeval u P ≠ 0 := fun h => hL.ne_zero 3 (by simp [h])
  have hQu : aeval u Q ≠ 0 := fun h => hL.ne_zero 3 (by simp [h])
  have hx1 : aeval u P / aeval u Q * (aeval u Q / u) = aeval u P / u := by field_simp
  have hx2 : aeval u P / aeval u Q * (aeval u Q * aeval u R₁ / (u * aeval u P)) = aeval u R₁ / u := by
    field_simp
  have hx3 : aeval u P / aeval u Q *
      (aeval u Q * (aeval u Q * aeval u R₁ + aeval u P * aeval u R₂) / (u * aeval u P ^ 2)) =
      aeval u Q * aeval u R₁ / (u * aeval u P) + aeval u R₂ / u := by
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro k hk
    simp only [Fin.sum_univ_two, Subfield.smul_def, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one] at hk
    have h := mod_H0 hu0 hL (natDegree_C_mul_le (k 1) R₂ |>.trans hR₂) (k 1) (k 0) (by
      simp only [map_mul, aeval_C, am]
      linear_combination (aeval u Q * (aeval u Q * aeval u R₁ + aeval u P * aeval u R₂) /
        (u * aeval u P ^ 2)) * hk - (k 1 : ℂ) * hx3)
    intro i; fin_cases i
    exacts [h.2.1, h.1]
  · rw [Fintype.linearIndependent_iff]
    intro k hk
    simp only [Fin.sum_univ_three, Subfield.smul_def, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hk
    have h := mod_H0 hu0 hL ((natDegree_C_mul_le (k 0) Q).trans hQ2) (k 1) (k 2) (by
      simp only [map_mul, aeval_C, am]
      linear_combination hk)
    have h0 : k 0 = 0 := by
      have := h.2.2
      simp only [map_mul, aeval_C, am, mul_eq_zero, hQu, or_false] at this
      exact_mod_cast this
    intro i; fin_cases i
    exacts [h0, h.1, h.2.1]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul]
    · exact mem_div_u hu0 hQ2
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · rw [hx1]; exact mem_div_u hu0 hP2
    · rw [hx2]; exact mem_div_u hu0 hR₁
    · rw [hx3]; exact add_mem (Submodule.subset_span (by simp)) (mem_div_u hu0 hR₂)
