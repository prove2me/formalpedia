-- Prove2me | solution 1 for DiazModulus.invisible_cyclic_space_u_multiplier_space_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:30:19.938761+00:00
-- url     : https://prove2.me/submissions/19b13eab-3412-4bfa-bb66-cd0102838271

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_binary_quadratic_dvd_of_coprime_mul_eq
import Theorems.Thm_DiazModulus_quadratic_space_mem_iff_numerator
import Theorems.Thm_DiazModulus_u_multiplier_space_le_span_no_degree_one_no_visible_element

open Complex ComplexConjugate

/-! # Q1.5, cyclic case: an invisible `WB` has `WB ∩ u⁻¹ WB = span(1, u⁻¹)`

By `quadratic_space_mem_iff_numerator`, `f ∈ WB` means
`f · u P² = (P² A + a₁ P Q S₁ + a₂ Q (Q S₁ + P S₂))(u)` with `deg A ≤ 2`. **Core:** if
`P² A + P Q S₁ L₁ + Q (Q S₁ + P S₂) L₂ = 0` with `deg Lᵢ ≤ e ≤ 1` and `deg A ≤ 2 + e`, then
`L₁ = L₂ = 0`. Indeed `Q² S₁ L₂ = −P (P A + Q S₁ L₁ + Q S₂ L₂)`, and
`binary_quadratic_dvd_of_coprime_mul_eq` at `P` (`F = Q² S₁`, `d = 6`; the right factor has degree
`≤ 4 + e` because `deg S₂ ≤ 2`) gives `L₂ = 0`. Then `P A + Q S₁ L₁ = 0`, and the same lemma with
`F = Q S₁`, `d = 4` gives `L₁ = 0`. The hypothesis `deg P = 2 ∨ deg F = d` holds because `deg P < 2`
forces `deg Q = 2` and, by `hP2`, `deg S₁ = 2`.
* `finrank = 5`: a relation among `1, u, u⁻¹, g₁, g₂` is the core with `e = 0`.
* If `f, u f ∈ WB`, subtracting the numerators gives the core with `e = 1`; so `a₁ = a₂ = 0` and
  `X A = A′`, hence `A.coeff 2 = 0` and `f = A(u)/u ∈ span(1, u⁻¹)`.
* `¬ D1` is `u_multiplier_space_le_span_no_degree_one_no_visible_element`. -/

namespace R21b_Q5b

open DiazModulus Polynomial

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem smul_def' (c : ↥Qbar) (z : ℂ) : c • z = (c : ℂ) * z := rfl

theorem u_ne_zero {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)

theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {p : (↥Qbar)[X]} (h : aeval u p = 0) : p = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) p h

theorem q_ne_zero {p q : (↥Qbar)[X]} (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) : q ≠ 0 := by
  rintro rfl
  have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop)
  simp at hdeg
  omega

/-- `deg P < 2` forces `deg Q = 2` and `deg S = 2`. -/
theorem deg_cond {P Q S : (↥Qbar)[X]} (hdeg : max P.natDegree Q.natDegree = 2) (hS : S.natDegree ≤ 2)
    (hP2 : P.coeff 2 ≠ 0 ∨ S.coeff 2 ≠ 0) :
    P.natDegree = 2 ∨ (Q.natDegree = 2 ∧ S.natDegree = 2 ∧ S ≠ 0) := by
  by_cases h : P.natDegree = 2
  · exact Or.inl h
  have hP : P.natDegree < 2 := lt_of_le_of_ne (hdeg ▸ le_max_left _ _) h
  have hS2 := hP2.resolve_left fun h' => h' (coeff_eq_zero_of_natDegree_lt hP)
  exact Or.inr ⟨by omega, le_antisymm hS (le_natDegree_of_ne_zero hS2), fun h0 => by simp [h0] at hS2⟩

theorem s_ne_zero {P S : (↥Qbar)[X]} (hPS : IsCoprime P S) (hP2 : P.coeff 2 ≠ 0 ∨ S.coeff 2 ≠ 0) :
    S ≠ 0 := by
  rintro rfl
  have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hPS)
  simp [coeff_eq_zero_of_natDegree_lt (show P.natDegree < 2 by omega)] at hP2

/-- The degree budget leaves no room: `L = 0`. -/
theorem kl_zero {P L : (↥Qbar)[X]} {e : ℕ} (he : e ≤ 1)
    (h : ∃ L₀ : (↥Qbar)[X], L = P * L₀ ∧ (L₀ = 0 ∨ L₀.natDegree + 2 ≤ e)) : L = 0 := by
  obtain ⟨L₀, hL, rfl | h0⟩ := h
  · simpa using hL
  · omega

/-- The core. -/
theorem core {P Q S₁ S₂ A L₁ L₂ : (↥Qbar)[X]} {e : ℕ} (he : e ≤ 1) (hcop : IsCoprime P Q)
    (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (hPS : IsCoprime P S₁) (hP2 : P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0)
    (hA : A.natDegree ≤ 2 + e) (hL₁ : L₁.natDegree ≤ e) (hL₂ : L₂.natDegree ≤ e)
    (h : P ^ 2 * A + P * Q * S₁ * L₁ + Q * (Q * S₁ + P * S₂) * L₂ = 0) : L₁ = 0 ∧ L₂ = 0 := by
  have hQ0 := q_ne_zero hcop hdeg
  have hP0 := q_ne_zero hcop.symm (by rw [max_comm]; exact hdeg)
  have hS0 := s_ne_zero hPS hP2
  have hP : P.natDegree ≤ 2 := hdeg ▸ le_max_left _ _
  have hQ : Q.natDegree ≤ 2 := hdeg ▸ le_max_right _ _
  have h2 : L₂ = 0 := kl_zero he (binary_quadratic_dvd_of_coprime_mul_eq P (Q ^ 2 * S₁) L₂
    (-(P * A + Q * S₁ * L₁ + Q * S₂ * L₂)) 6 e (hcop.pow_right.mul_right hPS)
    (mul_ne_zero (pow_ne_zero 2 hQ0) hS0)
    ((deg_cond hdeg hS₁ hP2).imp_right fun ⟨h1, h2, _⟩ => by
      rw [natDegree_mul (pow_ne_zero 2 hQ0) hS0, natDegree_pow]; omega) hL₂
    (by
      have h1 := natDegree_mul_le_of_le hP hA
      have h2 := natDegree_mul_le_of_le (natDegree_mul_le_of_le hQ hS₁) hL₁
      have h3 := natDegree_mul_le_of_le (natDegree_mul_le_of_le hQ hS₂) hL₂
      have h4 := natDegree_add_le (P * A + Q * S₁ * L₁) (Q * S₂ * L₂)
      have h5 := natDegree_add_le (P * A) (Q * S₁ * L₁)
      rw [natDegree_neg]
      omega)
    (by linear_combination h))
  have h' : P * A + Q * S₁ * L₁ = 0 :=
    mul_left_cancel₀ hP0 (by rw [h2] at h; linear_combination h)
  refine ⟨kl_zero he (binary_quadratic_dvd_of_coprime_mul_eq P (Q * S₁) L₁ (-A) 4 e
    (hcop.mul_right hPS) (mul_ne_zero hQ0 hS0)
    ((deg_cond hdeg hS₁ hP2).imp_right fun ⟨h1, h2, _⟩ => by
      rw [natDegree_mul hQ0 hS0]; omega) hL₁ (by rw [natDegree_neg]; omega)
    (by linear_combination h')), h2⟩

theorem quad_eval (u : ℂ) {A : (↥Qbar)[X]} (hA : A.natDegree ≤ 2) :
    aeval u A = (A.coeff 0 : ℂ) + (A.coeff 1 : ℂ) * u + (A.coeff 2 : ℂ) * u ^ 2 := by
  rw [aeval_eq_sum_range' (n := 3) (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, smul_def']
  ring

end R21b_Q5b

open DiazModulus R21b_Q5b in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (P Q S₁ S₂ : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (hPS : IsCoprime P S₁) (hP2 : P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0) :
    Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ)) = 5 ∧
    (∀ f : ℂ, (f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ) ∧
      u * f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ)) ↔
      f ∈ Submodule.span Qbar ({1, u⁻¹} : Set ℂ)) ∧
    ¬ (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ) ∧ u * t j ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ)) := by
  have hu0 := u_ne_zero hu
  have hQ0 := q_ne_zero hcop hdeg
  have hP0 := q_ne_zero hcop.symm (by rw [max_comm]; exact hdeg)
  have hPu : aeval u P ≠ 0 := fun h => hP0 (aeval_eq_zero hu h)
  have hMB := (quadratic_space_mem_iff_numerator u hu P Q S₁ S₂ hP0 hQ0).2
  set g₁ := aeval u Q * aeval u S₁ / (u * aeval u P) with hg₁
  set g₂ := aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2) with hg₂
  set W := Submodule.span Qbar ({1, u, u⁻¹, g₁, g₂} : Set ℂ) with hW
  have hmem : ∀ x ∈ ({1, u, u⁻¹, g₁, g₂} : Set ℂ), x ∈ W := fun x hx => Submodule.subset_span hx
  -- the `u`-multiplier space
  have hZ : ∀ f : ℂ, (f ∈ W ∧ u * f ∈ W) ↔ f ∈ Submodule.span Qbar ({1, u⁻¹} : Set ℂ) := by
    intro f
    constructor
    · rintro ⟨hf, huf⟩
      obtain ⟨A, a₁, a₂, hA, he⟩ := (hMB f).1 hf
      obtain ⟨A', a₁', a₂', hA', he'⟩ := (hMB (u * f)).1 huf
      have hpoly : P ^ 2 * (X * A - A') + P * Q * S₁ * (C a₁ * X - C a₁') +
          Q * (Q * S₁ + P * S₂) * (C a₂ * X - C a₂') = 0 := by
        apply aeval_eq_zero hu
        have e1 : u * (f * (u * aeval u P ^ 2)) = u * f * (u * aeval u P ^ 2) := by ring
        rw [he, he'] at e1
        simp only [map_add, map_mul, map_sub, map_pow, aeval_X, aeval_C, am] at e1 ⊢
        linear_combination e1
      obtain ⟨h1, h2⟩ := core le_rfl hcop hdeg hS₁ hS₂ hPS hP2
        ((natDegree_sub_le _ _).trans (max_le
          ((natDegree_mul_le_of_le natDegree_X_le hA).trans (by omega)) (by omega)))
        (by compute_degree) (by compute_degree) hpoly
      have ha₁ : a₁ = 0 := by simpa using congrArg (coeff · 1) h1
      have ha₂ : a₂ = 0 := by simpa using congrArg (coeff · 1) h2
      rw [h1, h2, mul_zero, mul_zero, add_zero, add_zero] at hpoly
      have hXA : X * A = A' :=
        sub_eq_zero.1 ((mul_eq_zero.1 hpoly).resolve_left (pow_ne_zero 2 hP0))
      have hA2 : A.coeff 2 = 0 := by
        have := congrArg (coeff · 3) hXA
        simp only [coeff_X_mul] at this
        rw [this]
        exact coeff_eq_zero_of_natDegree_lt (by omega)
      rw [ha₁, ha₂] at he
      simp only [map_add, map_mul, map_pow, map_zero, quad_eval u hA, hA2] at he
      refine Submodule.mem_span_pair.2 ⟨A.coeff 1, A.coeff 0, ?_⟩
      rw [smul_def', smul_def']
      apply mul_right_cancel₀ (mul_ne_zero hu0 (pow_ne_zero 2 hPu))
      rw [he]
      push_cast
      field_simp
      ring
    · intro hf
      obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hf
      have e : u * (c • (1 : ℂ) + d • u⁻¹) = c • u + d • (1 : ℂ) := by
        simp only [smul_def']
        field_simp
      rw [e]
      exact ⟨W.add_mem (W.smul_mem _ (hmem 1 (by simp))) (W.smul_mem _ (hmem u⁻¹ (by simp))),
        W.add_mem (W.smul_mem _ (hmem u (by simp))) (W.smul_mem _ (hmem 1 (by simp)))⟩
  -- the five generators are free
  have hli : LinearIndependent (↥Qbar) ![1, u, u⁻¹, g₁, g₂] := by
    rw [Fintype.linearIndependent_iff]
    intro s hs
    have hs' : (s 0 : ℂ) + s 1 * u + s 2 * u⁻¹ + s 3 * g₁ + s 4 * g₂ = 0 := by
      simpa [Fin.sum_univ_five, smul_def'] using hs
    have hpoly : P ^ 2 * (C (s 2) + C (s 0) * X + C (s 1) * X ^ 2) + P * Q * S₁ * C (s 3) +
        Q * (Q * S₁ + P * S₂) * C (s 4) = 0 := by
      apply aeval_eq_zero hu
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, am]
      linear_combination (norm := skip) (u * aeval u P ^ 2) * hs'
      rw [hg₁, hg₂]
      field_simp
      ring
    obtain ⟨h1, h2⟩ := core (e := 0) zero_le_one hcop hdeg hS₁ hS₂ hPS hP2 (by compute_degree!)
      (by simp) (by simp) hpoly
    rw [h1, h2, mul_zero, mul_zero, add_zero, add_zero] at hpoly
    have hA := (mul_eq_zero.1 hpoly).resolve_left (pow_ne_zero 2 hP0)
    have c0 : s 2 = 0 := by simpa using congrArg (coeff · 0) hA
    have c1 : s 0 = 0 := by simpa using congrArg (coeff · 1) hA
    have c2 : s 1 = 0 := by simpa using congrArg (coeff · 2) hA
    rw [C_eq_zero] at h1 h2
    intro i
    fin_cases i
    exacts [c1, c2, c0, h1, h2]
  have hset : ({1, u, u⁻¹, g₁, g₂} : Set ℂ) = Set.range ![1, u, u⁻¹, g₁, g₂] := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons,
      Matrix.range_empty, Set.union_empty]
    rfl
  refine ⟨?_, hZ, (u_multiplier_space_le_span_no_degree_one_no_visible_element u hu W
    (hmem u (by simp)) (hmem u⁻¹ (by simp)) fun f hf huf => (hZ f).1 ⟨hf, huf⟩).1⟩
  rw [hW, hset, finrank_span_eq_card hli, Fintype.card_fin]
