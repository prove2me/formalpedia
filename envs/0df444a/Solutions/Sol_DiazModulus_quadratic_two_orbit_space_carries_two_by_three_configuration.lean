-- Prove2me | solution 1 for DiazModulus.quadratic_two_orbit_space_carries_two_by_three_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:27:25.057527+00:00
-- url     : https://prove2.me/submissions/a6833cce-a1eb-4fc6-bc38-83b18c568c92

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The two-orbit space carries a 2 × 3 configuration

Write `H₀ = ⟨1, u, u⁻¹⟩`, `g₁ = Q R₁/(uP)`, `g₂ = P R₂/(uQ)` (values at `u`). Since the span of the
five generators has dimension 5, the family `1, u, u⁻¹, g₁, g₂` is free
(`linearIndependent_iff_card_eq_finrank_span`); in particular `g₁, g₂ ≠ 0`, so `P(u), Q(u) ≠ 0`.
Every `R(u)/u` with `deg R ≤ 2` lies in `H₀` (`aeval_eq_sum_range'`), so a relation
`R(u)/u + a g₁ + b g₂ = 0` forces `a = b = 0` and `R(u) = 0`. The products are explicit:
`(P/Q)(Q/u) = P/u`, `(P/Q)(R₂/u) = g₂`, `(P/Q) g₁ = R₁/u`, and the row `1` gives `Q/u, R₂/u, g₁`.
Independence of `x = (1, P/Q)`: multiplying `a + b P/Q = 0` by `R₂/u` gives `a R₂/u + b g₂ = 0`, so
`b = 0`, then `a = 0`. Independence of `y = (Q/u, R₂/u, g₁)`: the `g₁`-coefficient of a relation
vanishes; multiplying the relation by `P/Q` gives `(a P + c R₁)/u + b g₂ = 0`, so `b = 0`; then
`a Q/u = 0` gives `a = 0`. No transcendence is needed beyond `u ≠ 0`.
-/

namespace R20_twoOrbit

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

end R20_twoOrbit

open DiazModulus R20_twoOrbit in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar)
    (P Q R₁ R₂ : (↥Qbar)[X]) (hdeg : max P.natDegree Q.natDegree = 2)
    (hR₁ : R₁.natDegree ≤ 2) (hR₂ : R₂.natDegree ≤ 2)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₁ / (u * aeval u P),
        aeval u P * aeval u R₂ / (u * aeval u Q)} : Set ℂ)) = 5) :
    LinearIndependent (↥Qbar) ![1, aeval u P / aeval u Q] ∧
    LinearIndependent (↥Qbar) ![aeval u Q / u, aeval u R₂ / u, aeval u Q * aeval u R₁ / (u * aeval u P)] ∧
    ∀ i j, ![1, aeval u P / aeval u Q] i *
      ![aeval u Q / u, aeval u R₂ / u, aeval u Q * aeval u R₁ / (u * aeval u P)] j ∈
      Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₁ / (u * aeval u P),
        aeval u P * aeval u R₂ / (u * aeval u Q)} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  have hL := indep5 h5
  have hP2 : P.natDegree ≤ 2 := hdeg ▸ le_max_left _ _
  have hQ2 : Q.natDegree ≤ 2 := hdeg ▸ le_max_right _ _
  have hPu : aeval u P ≠ 0 := fun h => hL.ne_zero 3 (by simp [h])
  have hQu : aeval u Q ≠ 0 := fun h => hL.ne_zero 4 (by simp [h])
  have hx1 : aeval u P / aeval u Q * (aeval u Q / u) = aeval u P / u := by field_simp
  have hx2 : aeval u P / aeval u Q * (aeval u R₂ / u) = aeval u P * aeval u R₂ / (u * aeval u Q) := by
    ring
  have hx3 : aeval u P / aeval u Q * (aeval u Q * aeval u R₁ / (u * aeval u P)) = aeval u R₁ / u := by
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro k hk
    simp only [Fin.sum_univ_two, Subfield.smul_def, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one] at hk
    have h1 := (mod_H0 hu0 hL (natDegree_C_mul_le (k 0) R₂ |>.trans hR₂) 0 (k 1) (by
      simp only [map_mul, aeval_C, am, Subfield.coe_zero, zero_mul, add_zero]
      linear_combination (aeval u R₂ / u) * hk)).2.1
    have h0 : k 0 = 0 := by simpa [h1] using hk
    intro i; fin_cases i <;> assumption
  · rw [Fintype.linearIndependent_iff]
    intro k hk
    simp only [Fin.sum_univ_three, Subfield.smul_def, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hk
    have hd1 : (C (k 0) * Q + C (k 1) * R₂).natDegree ≤ 2 :=
      natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans hQ2)
        ((natDegree_C_mul_le _ _).trans hR₂)
    have h2 := (mod_H0 hu0 hL hd1 (k 2) 0 (by
      simp only [map_add, map_mul, aeval_C, am, Subfield.coe_zero, zero_mul, add_zero]
      linear_combination hk)).1
    have hd2 : (C (k 0) * P + C (k 2) * R₁).natDegree ≤ 2 :=
      natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans hP2)
        ((natDegree_C_mul_le _ _).trans hR₁)
    have h1 := (mod_H0 hu0 hL hd2 0 (k 1) (by
      simp only [map_add, map_mul, aeval_C, am, Subfield.coe_zero, zero_mul, add_zero]
      linear_combination (aeval u P / aeval u Q) * hk - (k 0 : ℂ) * hx1 - (k 2 : ℂ) * hx3)).2.1
    have h0 : k 0 = 0 := by
      rw [h1, h2] at hk
      have : (k 0 : ℂ) * (aeval u Q / u) = 0 := by simpa using hk
      simpa [hQu, hu0] using this
    intro i; fin_cases i <;> assumption
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul]
    · exact mem_div_u hu0 hQ2
    · exact mem_div_u hu0 hR₂
    · exact Submodule.subset_span (by simp)
    · rw [hx1]; exact mem_div_u hu0 hP2
    · rw [hx2]; exact Submodule.subset_span (by simp)
    · rw [hx3]; exact mem_div_u hu0 hR₁
