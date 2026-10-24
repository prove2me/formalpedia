-- Prove2me | solution 1 for DiazModulus.quadratic_complement_eigen_forms
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:29:39.859907+00:00
-- url     : https://prove2.me/submissions/c25a49e8-5dae-4d1e-b5b9-9cfe69498684

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_qbar_matrix_fin_two_eigen_or_jordan
import Theorems.Thm_DiazModulus_quadratic_complement_multiplication_matrix

open Complex ComplexConjugate

/-! # Step 4 of Theorem NF: scalar, two eigenvectors, or one Jordan pair

Let `S = span_Q̄ (1, u, u⁻¹, g₀, g₁)`, `k = P(u)/Q(u)` and `P_c = P(u) − c Q(u)`; `Q ≠ 0` and
`P − cQ ≠ 0` by coprimality and degree 2, so `Q(u), P_c ≠ 0` as `u` is transcendental.
`quadratic_complement_multiplication_matrix` gives `T`, `Rⱼ` with `k gⱼ = Rⱼ(u)/u + Σᵢ Tᵢⱼ gᵢ`.
With `G x = x₀ g₀ + x₁ g₁` and `H x = x₀ R₀ + x₁ R₁` this reads `k G x = H x(u)/u + G (T x)`; so
`T x = c x + y` gives `G x = Q(u)(H x(u) + u G y)/(u P_c)`. Apply
`qbar_matrix_fin_two_eigen_or_jordan` to `T`.
- Eigenvectors `v, w`: `G v`, `G w` have the stated forms, and since `v, w` span `Q̄²`,
  `span(1, u, u⁻¹, G v, G w) = S`.
- Jordan pair: `G v` as above and `G w = Q(u)(Q(u) R₀(u) + P_c R₁(u))/(u P_c²)`; same span.
- Scalar `T = c`: `(k − c)` sends `g₀, g₁, Q(u)/u` to `R₀(u)/u, R₁(u)/u, (P − cQ)(u)/u`, which are
  independent (by the independence of the five generators of `S`), so they span the
  3-dimensional `H₀ = span(1, u, u⁻¹)`. Every `R(u)/u` (`deg R ≤ 2`) is then
  `(k − c)(α₀ g₀ + α₁ g₁ + α₂ Q(u)/u)`, and `Q(u)R(u)/(u P_c) = α₀ g₀ + α₁ g₁ + α₂ Q(u)/u ∈ S`. -/

namespace R20_eigen

open DiazModulus Polynomial

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem sm (a : ↥Qbar) (z : ℂ) : a • z = (a : ℂ) * z := rfl

theorem aeval_ne_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (hP : P ≠ 0) :
    aeval u P ≠ 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact fun h => hP (transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h)

theorem div_u {u : ℂ} (hu0 : u ≠ 0) {R : (↥Qbar)[X]} (hR : R.natDegree ≤ 2) :
    aeval u R / u = (R.coeff 1 : ℂ) + (R.coeff 2 : ℂ) * u + (R.coeff 0 : ℂ) * u⁻¹ := by
  rw [aeval_eq_sum_range' (n := 3) (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sm, pow_zero, pow_one]
  field_simp
  ring

theorem eig_form {k Pu Qu u x r y c : ℂ} (hk : k = Pu / Qu) (hQ : Qu ≠ 0)
    (hPc : Pu - c * Qu ≠ 0) (hu0 : u ≠ 0) (h : k * x = r / u + (c * x + y)) :
    x = Qu * (r + u * y) / (u * (Pu - c * Qu)) := by
  subst hk
  rw [eq_div_iff (mul_ne_zero hu0 hPc)]
  have e1 : Pu / Qu * x * (Qu * u) = Pu * x * u := by field_simp
  have e2 : (r / u + (c * x + y)) * (Qu * u) = (r + (c * x + y) * u) * Qu := by field_simp
  linear_combination (Qu * u) * h - e1 + e2

theorem jordan_alg {Qu D u a b : ℂ} (hD : D ≠ 0) (hu0 : u ≠ 0) :
    Qu * (b + u * (Qu * a / (u * D))) / (u * D) = Qu * (Qu * a + D * b) / (u * D ^ 2) := by
  field_simp
  ring

theorem scal_alg {Qu D u r Y : ℂ} (hQ : Qu ≠ 0) (hD : D ≠ 0) (hu0 : u ≠ 0)
    (h : D / Qu * Y = r / u) : Qu * r / (u * D) = Y := by
  have e1 : D / Qu * Y * (Qu * u) = D * Y * u := by field_simp
  have e2 : r / u * (Qu * u) = r * Qu := by field_simp
  rw [div_eq_iff (mul_ne_zero hu0 hD)]
  linear_combination -(Qu * u) * h + e1 - e2

theorem lin5 {u : ℂ} {g : Fin 2 → ℂ}
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ)) = 5)
    (a₁ a₂ a₃ a₄ a₅ : ↥Qbar) (h : (a₁ : ℂ) + a₂ * u + a₃ * u⁻¹ + a₄ * g 0 + a₅ * g 1 = 0) :
    a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 ∧ a₅ = 0 := by
  have hli : LinearIndependent (↥Qbar) ![(1 : ℂ), u, u⁻¹, g 0, g 1] := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank]
    have hr : Set.range ![(1 : ℂ), u, u⁻¹, g 0, g 1] = {1, u, u⁻¹, g 0, g 1} := by
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
    rw [hr, h5]
    simp
  have := Fintype.linearIndependent_iff.1 hli ![a₁, a₂, a₃, a₄, a₅]
    (by simp only [Fin.sum_univ_five, sm]; simp; linear_combination h)
  exact ⟨this 0, this 1, this 2, this 3, this 4⟩

theorem span_swap {u : ℂ} (g : Fin 2 → ℂ) {v w : Fin 2 → ↥Qbar}
    (hli : LinearIndependent (↥Qbar) ![v, w]) :
    Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ) =
      Submodule.span Qbar ({1, u, u⁻¹, Fintype.linearCombination (↥Qbar) g v,
        Fintype.linearCombination (↥Qbar) g w} : Set ℂ) := by
  set G := Fintype.linearCombination (↥Qbar) g
  have htop : Submodule.span (↥Qbar) ({v, w} : Set (Fin 2 → ↥Qbar)) = ⊤ := by
    have := hli.span_eq_top_of_card_eq_finrank (by simp)
    have h2 : Submodule.span (↥Qbar) ({w, v} : Set (Fin 2 → ↥Qbar)) = ⊤ := by
      simpa [Matrix.range_cons, Matrix.range_empty, Set.singleton_union] using this
    rwa [Set.pair_comm] at h2
  apply le_antisymm
  · have hg : ∀ j, g j ∈ Submodule.span Qbar ({1, u, u⁻¹, G v, G w} : Set ℂ) := by
      intro j
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1
        (htop ▸ Submodule.mem_top (x := (Pi.single j 1 : Fin 2 → ↥Qbar)))
      have : g j = G (Pi.single j 1) := by simp [G]
      rw [this, ← hab, map_add, map_smul, map_smul]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact hg 0
    · exact hg 1
  · have hG : ∀ x, G x ∈ Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ) := by
      intro x
      rw [Fintype.linearCombination_apply, Fin.sum_univ_two]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact hG v
    · exact hG w

end R20_eigen

open DiazModulus R20_eigen in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (P Q : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (g : Fin 2 → ℂ)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ)) = 5)
    (hk : ∀ j, aeval u P / aeval u Q * g j ∈ Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ)) :
    (∃ c : ↥Qbar, ∀ R : (↥Qbar)[X], R.natDegree ≤ 2 → aeval u Q * aeval u R / (u * (aeval u P - (c : ℂ) * aeval u Q)) ∈
        Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ)) ∨
    (∃ c₁ c₂ : ↥Qbar, c₁ ≠ c₂ ∧ ∃ R₁ R₂ : (↥Qbar)[X], R₁.natDegree ≤ 2 ∧ R₂.natDegree ≤ 2 ∧
        Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₁ / (u * (aeval u P - (c₁ : ℂ) * aeval u Q)),
          aeval u Q * aeval u R₂ / (u * (aeval u P - (c₂ : ℂ) * aeval u Q))} : Set ℂ)) ∨
    (∃ c : ↥Qbar, ∃ R₀ R₁ : (↥Qbar)[X], R₀.natDegree ≤ 2 ∧ R₁.natDegree ≤ 2 ∧
        Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₀ / (u * (aeval u P - (c : ℂ) * aeval u Q)),
          aeval u Q * (aeval u Q * aeval u R₀ + (aeval u P - (c : ℂ) * aeval u Q) * aeval u R₁) / (u * (aeval u P - (c : ℂ) * aeval u Q) ^ 2)} :
            Set ℂ)) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  have hQ : Q ≠ 0 := by
    rintro rfl
    have h0 := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop)
    simp [h0] at hdeg
  have hP2 : P.natDegree ≤ 2 := hdeg ▸ le_max_left _ _
  have hQ2 : Q.natDegree ≤ 2 := hdeg ▸ le_max_right _ _
  have hPc : ∀ c : ↥Qbar, P - C c * Q ≠ 0 := by
    intro c h
    rw [sub_eq_zero] at h
    subst h
    have h0 := natDegree_eq_zero_of_isUnit (hcop.isUnit_of_dvd' (dvd_mul_left _ _) dvd_rfl)
    have h1 : (C c * Q).natDegree = 0 := Nat.le_zero.1 ((natDegree_C_mul_le c Q).trans h0.le)
    rw [h0, h1] at hdeg
    simp at hdeg
  have hQu : aeval u Q ≠ 0 := aeval_ne_zero hu hQ
  have hPcu : ∀ c : ↥Qbar, aeval u P - (c : ℂ) * aeval u Q ≠ 0 := fun c => by
    simpa [am] using aeval_ne_zero hu (hPc c)
  obtain ⟨T, R, hR⟩ := DiazModulus.quadratic_complement_multiplication_matrix u
    (aeval u P / aeval u Q) hu g hk
  set k := aeval u P / aeval u Q with hkdef
  set S := Submodule.span (↥Qbar) ({1, u, u⁻¹, g 0, g 1} : Set ℂ) with hS
  set G := Fintype.linearCombination (↥Qbar) g with hGdef
  have hG : ∀ x, G x = (x 0 : ℂ) * g 0 + (x 1 : ℂ) * g 1 := fun x => by
    simp [G, Fintype.linearCombination_apply, Fin.sum_univ_two, sm]
  set H : (Fin 2 → ↥Qbar) → (↥Qbar)[X] := fun x => C (x 0) * R 0 + C (x 1) * R 1 with hHdef
  have hHdeg : ∀ x, (H x).natDegree ≤ 2 := fun x =>
    (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans (hR 0).1)
      ((natDegree_C_mul_le _ _).trans (hR 1).1))
  have hkG : ∀ x, k * G x = aeval u (H x) / u + G (T.mulVec x) := by
    intro x
    rw [hG, hG]
    have e0 := (hR 0).2
    have e1 := (hR 1).2
    simp only [H, map_add, map_mul, aeval_C, am, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    push_cast
    linear_combination (x 0 : ℂ) * e0 + (x 1 : ℂ) * e1
  have hform : ∀ (c : ↥Qbar) x y, T.mulVec x = c • x + y →
      G x = aeval u Q * (aeval u (H x) + u * G y) / (u * (aeval u P - (c : ℂ) * aeval u Q)) := by
    intro c x y hxy
    apply eig_form hkdef hQu (hPcu c) hu0
    rw [hkG, hxy, G.map_add, G.map_smul, sm]
  rcases DiazModulus.qbar_matrix_fin_two_eigen_or_jordan T with
    ⟨c, hc⟩ | ⟨v, w, c₁, c₂, hne, hli, hv, hw⟩ | ⟨v, w, c, hli, hv, hw⟩
  · left
    refine ⟨c, ?_⟩
    set Pcu := aeval u P - (c : ℂ) * aeval u Q with hPcudef
    have hPc0 : Pcu ≠ 0 := hPcu c
    have hRj : ∀ j, aeval u (R j) / u = Pcu / aeval u Q * g j := by
      intro j
      have hgj : g j = aeval u Q * (aeval u (R j) + u * 0) / (u * Pcu) := by
        apply eig_form hkdef hQu (hPcu c) hu0
        rw [(hR j).2, hc]
        fin_cases j <;> simp
      rw [hgj, mul_zero, add_zero]
      field_simp
    have hQP : aeval u (P - C c * Q) / u = Pcu / aeval u Q * (aeval u Q / u) := by
      rw [map_sub, map_mul, aeval_C, am, ← hPcudef]
      field_simp
    set ε := Pcu / aeval u Q with hεdef
    have hε : ε ≠ 0 := div_ne_zero (hPcu c) hQu
    set H0 := Submodule.span (↥Qbar) (Set.range ![(1 : ℂ), u, u⁻¹]) with hH0def
    have : FiniteDimensional (↥Qbar) H0 :=
      FiniteDimensional.span_of_finite (↥Qbar) (Set.finite_range _)
    have hH0 : Module.finrank (↥Qbar) H0 = 3 := by
      rw [finrank_span_eq_card]
      · simp
      · rw [Fintype.linearIndependent_iff]
        intro α hα
        simp only [Fin.sum_univ_three, sm] at hα
        simp at hα
        obtain ⟨h1, h2, h3, -, -⟩ := lin5 h5 (α 0) (α 1) (α 2) 0 0
          (by push_cast; linear_combination hα)
        intro i; fin_cases i <;> simp [h1, h2, h3]
    have memH0 : ∀ R' : (↥Qbar)[X], R'.natDegree ≤ 2 → aeval u R' / u ∈ H0 := by
      intro R' hR'
      rw [div_u hu0 hR']
      exact (Submodule.mem_span_range_iff_exists_fun (↥Qbar)).2
        ⟨![R'.coeff 1, R'.coeff 2, R'.coeff 0], by simp [Fin.sum_univ_three, sm]⟩
    have hH0S : H0 ≤ S := by
      rw [Submodule.span_le, Set.range_subset_iff]
      intro i; fin_cases i <;> exact Submodule.subset_span (by simp)
    have hdegPc : (P - C c * Q).natDegree ≤ 2 :=
      (natDegree_sub_le _ _).trans (max_le hP2 ((natDegree_C_mul_le _ _).trans hQ2))
    set b : Fin 3 → ℂ := ![g 0, g 1, aeval u Q / u] with hbdef
    have hsum : ∀ α : Fin 3 → ↥Qbar, ∑ i, α i • (ε * b i) =
        ε * ((α 0 : ℂ) * g 0 + α 1 * g 1 + α 2 * (aeval u Q / u)) := by
      intro α
      simp [Fin.sum_univ_three, sm, b]
      ring
    have hQd := div_u hu0 hQ2
    have hfli : LinearIndependent (↥Qbar) (fun i => ε * b i) := by
      rw [Fintype.linearIndependent_iff]
      intro α hα
      rw [hsum] at hα
      have h' := (mul_eq_zero.1 hα).resolve_left hε
      rw [hQd] at h'
      obtain ⟨h1, h2, h3, h4, h5'⟩ := lin5 h5 (α 2 * Q.coeff 1) (α 2 * Q.coeff 2)
        (α 2 * Q.coeff 0) (α 0) (α 1) (by push_cast; linear_combination h')
      have hα2 : α 2 = 0 := by
        by_contra hne
        apply hQu
        have q1 := (mul_eq_zero.1 h1).resolve_left hne
        have q2 := (mul_eq_zero.1 h2).resolve_left hne
        have q0 := (mul_eq_zero.1 h3).resolve_left hne
        have : aeval u Q / u = 0 := by rw [hQd, q0, q1, q2]; simp
        exact (div_eq_zero_iff.1 this).resolve_right hu0
      intro i; fin_cases i <;> simp [h4, h5', hα2]
    have hV : Submodule.span (↥Qbar) (Set.range (fun i => ε * b i)) = H0 := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le, Set.range_subset_iff]
        intro i; fin_cases i
        · show ε * g 0 ∈ H0
          rw [← hRj 0]; exact memH0 _ (hR 0).1
        · show ε * g 1 ∈ H0
          rw [← hRj 1]; exact memH0 _ (hR 1).1
        · show ε * (aeval u Q / u) ∈ H0
          rw [← hQP]; exact memH0 _ hdegPc
      · rw [finrank_span_eq_card hfli, hH0]; simp
    intro R' hR'
    have hm := memH0 R' hR'
    rw [← hV] at hm
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun (↥Qbar)).1 hm
    rw [hsum] at hα
    rw [scal_alg hQu (hPcu c) hu0 hα]
    have hQS : aeval u Q / u ∈ S := hH0S (memH0 Q hQ2)
    exact add_mem (add_mem (Submodule.smul_mem S (α 0) (Submodule.subset_span (by simp)))
      (Submodule.smul_mem S (α 1) (Submodule.subset_span (by simp)))) (Submodule.smul_mem S (α 2) hQS)
  · right; left
    refine ⟨c₁, c₂, hne, H v, H w, hHdeg v, hHdeg w, ?_⟩
    have hv' := hform c₁ v 0 (by rw [hv, add_zero])
    have hw' := hform c₂ w 0 (by rw [hw, add_zero])
    rw [map_zero, mul_zero, add_zero] at hv' hw'
    rw [← hv', ← hw']
    exact span_swap g hli
  · right; right
    refine ⟨c, H v, H w, hHdeg v, hHdeg w, ?_⟩
    have hv' := hform c v 0 (by rw [hv, add_zero])
    rw [map_zero, mul_zero, add_zero] at hv'
    have hw' := hform c w v hw
    have hw'' : G w = aeval u Q * (aeval u Q * aeval u (H v) +
        (aeval u P - (c : ℂ) * aeval u Q) * aeval u (H w)) /
          (u * (aeval u P - (c : ℂ) * aeval u Q) ^ 2) := by
      rw [hw', hv']
      exact jordan_alg (hPcu c) hu0
    rw [← hv', ← hw'']
    exact span_swap g hli
