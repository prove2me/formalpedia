-- Prove2me | solution 1 for DiazModulus.quadratic_eigen_forms_canonical
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:29:42.545519+00:00
-- url     : https://prove2.me/submissions/2c3e9e52-aa35-41c4-b0d4-4bcf8d6e02f5

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_coprime_pencil_mobius

open Complex ComplexConjugate

/-! # The eigen-forms in canonical coordinates

Write `H₀ = ⟨1, u, u⁻¹⟩` and `P_c = P − cQ`; by `coprime_pencil_mobius` every pencil
`P − cQ, P − c'Q` (`c ≠ c'`) and `P − cQ, Q` is again coprime of maximal degree 2.
* Scalar branch: `Q R/(u P_c) ∈ W` for all `deg R ≤ 2`. Take `t = (u⁻¹, 1, Q/(u P_c))`: then
  `u t = (1, u, Q·X/(u P_c))` lies in `W`. A relation `a u⁻¹ + b + e Q/(u P_c) = 0`, multiplied by
  `u P_c(u)`, gives `(a + bX) P_c + e Q = 0` in `Q̄[X]` since `u` is transcendental. Coprimality gives
  `P_c ∣ e`; if `e ≠ 0` then `deg P_c = 0`, `deg Q = 2`, while `Q = −e⁻¹(a + bX) P_c` has degree
  `≤ 1`; so `e = 0`, and `a + bX = 0`. This is D1.
* Two-orbit branch: with `P' = P − c₁Q`, `Q' = P − c₂Q`, `d = c₁ − c₂`, `S₁ = R₁/d`, `S₂ = −R₂/d`
  one has `Q' S₁/(uP') − Q R₁/(uP') = S₁/u` and `P' S₂/(uQ') − Q R₂/(uQ') = S₂/u`, both in `H₀`;
  so the two spans agree (D2a). The denominators are non-zero because the five generators of `W`
  are free (`finrank = 5`).
* Cyclic branch: `P' = P − cQ`, `Q' = Q`, `S₁ = R₀`, `S₂ = R₁` gives D2b verbatim.
-/

namespace R20_canon

open DiazModulus Polynomial

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) : P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

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

theorem mem_H0 {u : ℂ} (hu0 : u ≠ 0) {R : (↥Qbar)[X]} (hR : R.natDegree ≤ 2) :
    aeval u R / u ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) := by
  rw [div_u hu0 hR]
  refine add_mem (add_mem (cmul_mem _ ?_) (cmul_mem _ ?_)) (cmul_mem _ ?_) <;>
    exact Submodule.subset_span (by simp)

/-- Moving the last two generators along `⟨a, b, c⟩` does not change the span. -/
theorem span5_congr {a b c g₁ g₂ G₁ G₂ : ℂ}
    (h₁ : G₁ - g₁ ∈ Submodule.span Qbar ({a, b, c} : Set ℂ))
    (h₂ : G₂ - g₂ ∈ Submodule.span Qbar ({a, b, c} : Set ℂ)) :
    Submodule.span Qbar ({a, b, c, g₁, g₂} : Set ℂ) =
      Submodule.span Qbar ({a, b, c, G₁, G₂} : Set ℂ) := by
  have key : ∀ {x₁ x₂ y₁ y₂ : ℂ}, y₁ - x₁ ∈ Submodule.span Qbar ({a, b, c} : Set ℂ) →
      y₂ - x₂ ∈ Submodule.span Qbar ({a, b, c} : Set ℂ) →
      Submodule.span Qbar ({a, b, c, y₁, y₂} : Set ℂ) ≤
        Submodule.span Qbar ({a, b, c, x₁, x₂} : Set ℂ) := by
    intro x₁ x₂ y₁ y₂ e₁ e₂
    have hH : Submodule.span Qbar ({a, b, c} : Set ℂ) ≤
        Submodule.span Qbar ({a, b, c, x₁, x₂} : Set ℂ) :=
      Submodule.span_mono (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
    rw [Submodule.span_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    refine ⟨Submodule.subset_span (by simp), Submodule.subset_span (by simp),
      Submodule.subset_span (by simp), ?_, ?_⟩
    · simpa using add_mem (hH e₁) (Submodule.subset_span (by simp) : x₁ ∈ _)
    · simpa using add_mem (hH e₂) (Submodule.subset_span (by simp) : x₂ ∈ _)
  refine le_antisymm (key ?_ ?_) (key h₁ h₂)
  · rw [← neg_sub]; exact neg_mem h₁
  · rw [← neg_sub]; exact neg_mem h₂

theorem ne_zero_of_cop {K : Type*} [Field K] {p q : K[X]} (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) : p ≠ 0 := by
  rintro rfl
  have hq := natDegree_eq_zero_of_isUnit (isCoprime_zero_left.mp hcop)
  rw [hq, natDegree_zero] at hdeg
  exact absurd hdeg (by norm_num)

/-- `(a + bX) p + e q = 0` with `p, q` coprime of maximal degree 2 forces `a = b = e = 0`. -/
theorem poly_rel {K : Type*} [Field K] {p q : K[X]} (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) (a b e : K)
    (h : (C a + C b * X) * p + C e * q = 0) : a = 0 ∧ b = 0 ∧ e = 0 := by
  have he : e = 0 := by
    by_contra he
    have hdvd : p ∣ C e := hcop.dvd_of_dvd_mul_right ⟨-(C a + C b * X), by linear_combination h⟩
    have hp0 : p.natDegree = 0 :=
      natDegree_eq_zero_of_isUnit (isUnit_of_dvd_unit hdvd (isUnit_C.mpr (IsUnit.mk0 _ he)))
    have hq2 : q.natDegree = 2 := by rw [hp0] at hdeg; simpa using hdeg
    have hq : q = -(C e⁻¹ * (C a + C b * X)) * p := by
      have h' : C e * q = -((C a + C b * X) * p) := by linear_combination h
      calc q = C e⁻¹ * (C e * q) := by rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ he, C_1, one_mul]
        _ = _ := by rw [h']; ring
    have hle : q.natDegree ≤ 1 := by
      rw [hq]
      refine natDegree_mul_le.trans ?_
      rw [hp0, add_zero, natDegree_neg]
      compute_degree
    omega
  subst he
  have hp : p ≠ 0 := ne_zero_of_cop hcop hdeg
  have hl : C a + C b * X = 0 := by simpa [hp] using h
  have ha := congrArg (coeff · 0) hl
  have hb := congrArg (coeff · 1) hl
  simp at ha hb
  exact ⟨ha, hb, rfl⟩

theorem shift₁ {A B R c₁ c₂ u : ℂ} (h1 : A - c₁ * B ≠ 0) (hd : c₁ - c₂ ≠ 0) :
    (A - c₂ * B) * ((c₁ - c₂)⁻¹ * R) / (u * (A - c₁ * B)) - B * R / (u * (A - c₁ * B)) =
      (c₁ - c₂)⁻¹ * R / u := by
  rw [div_sub_div_same, ← mul_div_mul_right ((c₁ - c₂)⁻¹ * R) u h1]
  congr 1
  linear_combination (R * B) * inv_mul_cancel₀ hd

theorem shift₂ {A B R c₁ c₂ u : ℂ} (h2 : A - c₂ * B ≠ 0) (hd : c₁ - c₂ ≠ 0) :
    (A - c₁ * B) * (-(c₁ - c₂)⁻¹ * R) / (u * (A - c₂ * B)) - B * R / (u * (A - c₂ * B)) =
      -(c₁ - c₂)⁻¹ * R / u := by
  rw [div_sub_div_same, ← mul_div_mul_right (-(c₁ - c₂)⁻¹ * R) u h2]
  congr 1
  linear_combination (R * B) * inv_mul_cancel₀ hd

end R20_canon

open DiazModulus R20_canon in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W) (P Q : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2)
    (hform :
      (∃ c : ↥Qbar, ∀ R : (↥Qbar)[X], R.natDegree ≤ 2 → aeval u Q * aeval u R / (u * (aeval u P - (c : ℂ) * aeval u Q)) ∈
          W) ∨
      (∃ c₁ c₂ : ↥Qbar, c₁ ≠ c₂ ∧ ∃ R₁ R₂ : (↥Qbar)[X], R₁.natDegree ≤ 2 ∧ R₂.natDegree ≤ 2 ∧
          W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₁ / (u * (aeval u P - (c₁ : ℂ) * aeval u Q)),
            aeval u Q * aeval u R₂ / (u * (aeval u P - (c₂ : ℂ) * aeval u Q))} : Set ℂ)) ∨
      (∃ c : ↥Qbar, ∃ R₀ R₁ : (↥Qbar)[X], R₀.natDegree ≤ 2 ∧ R₁.natDegree ≤ 2 ∧
          W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₀ / (u * (aeval u P - (c : ℂ) * aeval u Q)),
            aeval u Q * (aeval u Q * aeval u R₀ + (aeval u P - (c : ℂ) * aeval u Q) * aeval u R₁) / (u * (aeval u P - (c : ℂ) * aeval u Q) ^ 2)} :
              Set ℂ))) :
    (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ W ∧ u * t j ∈ W) ∨ (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u P' * aeval u S₂ / (u * aeval u Q')} : Set ℂ)) ∨
    (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u Q' * (aeval u Q' * aeval u S₁ + aeval u P' * aeval u S₂) / (u * aeval u P' ^ 2)} :
            Set ℂ)) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  have hpc : ∀ c : ↥Qbar, aeval u (P + C (-c) * Q) = aeval u P - (c : ℂ) * aeval u Q := fun c => by
    simp only [map_add, map_mul, aeval_C, am]; push_cast; ring
  rcases hform with ⟨c, hc⟩ | ⟨c₁, c₂, hne, R₁, R₂, hR₁, hR₂, hWeq⟩ | ⟨c, R₀, R₁, hR₀, hR₁, hWeq⟩
  · -- scalar branch: D1
    left
    obtain ⟨hcop', hdeg'⟩ := DiazModulus.coprime_pencil_mobius P Q hcop hdeg 1 (-c) 0 1 (by simp)
    simp only [map_zero, zero_mul, zero_add, map_one, one_mul] at hcop' hdeg'
    have hD : aeval u P - (c : ℂ) * aeval u Q ≠ 0 := fun h =>
      ne_zero_of_cop hcop' hdeg' (aeval_eq_zero hu (by rw [hpc]; exact h))
    refine ⟨![u⁻¹, 1, aeval u Q / (u * (aeval u P - (c : ℂ) * aeval u Q))], ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro k hk
      simp only [Fin.sum_univ_three, Subfield.smul_def, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hk
      have e1 : u * (aeval u P - (c : ℂ) * aeval u Q) * u⁻¹ = aeval u P - (c : ℂ) * aeval u Q := by
        field_simp
      have e2 : u * (aeval u P - (c : ℂ) * aeval u Q) *
          (aeval u Q / (u * (aeval u P - (c : ℂ) * aeval u Q))) = aeval u Q := by field_simp
      have hF := aeval_eq_zero hu (P := (C (k 0) + C (k 1) * X) * (P + C (-c) * Q) + C (k 2) * Q) (by
        rw [map_add, map_mul, hpc]
        simp only [map_add, map_mul, aeval_C, aeval_X, am]
        linear_combination (u * (aeval u P - (c : ℂ) * aeval u Q)) * hk - (k 0 : ℂ) * e1 -
          (k 2 : ℂ) * e2)
      obtain ⟨h0, h1, h2⟩ := poly_rel hcop' hdeg' _ _ _ hF
      intro i; fin_cases i <;> assumption
    · intro j
      fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      · exact ⟨hui, by rw [mul_inv_cancel₀ hu0]; exact h1⟩
      · exact ⟨h1, by rw [mul_one]; exact hu1⟩
      · refine ⟨by simpa using hc 1 (by simp), ?_⟩
        have := hc X (natDegree_X_le.trans (by norm_num))
        rw [aeval_X] at this
        convert this using 1
        ring
  · -- two-orbit branch: D2a
    right; left
    obtain ⟨hcop', hdeg'⟩ := DiazModulus.coprime_pencil_mobius P Q hcop hdeg 1 (-c₁) 1 (-c₂)
      (by intro h; apply hne; linear_combination h)
    simp only [map_one, one_mul] at hcop' hdeg'
    have hd : (c₁ : ℂ) - c₂ ≠ 0 := sub_ne_zero.mpr (Subtype.coe_injective.ne hne)
    refine ⟨P + C (-c₁) * Q, P + C (-c₂) * Q, C (c₁ - c₂)⁻¹ * R₁, C (-(c₁ - c₂)⁻¹) * R₂, hcop',
      hdeg', (natDegree_C_mul_le _ _).trans hR₁, (natDegree_C_mul_le _ _).trans hR₂, ?_⟩
    subst hWeq
    have hL := indep5 hW
    have hD1 : aeval u P - (c₁ : ℂ) * aeval u Q ≠ 0 := fun h => hL.ne_zero 3 (by simp [h])
    have hD2 : aeval u P - (c₂ : ℂ) * aeval u Q ≠ 0 := fun h => hL.ne_zero 4 (by simp [h])
    have hS1 : aeval u (C (c₁ - c₂)⁻¹ * R₁) = ((c₁ : ℂ) - c₂)⁻¹ * aeval u R₁ := by
      simp only [map_mul, aeval_C, am]; push_cast; ring
    have hS2 : aeval u (C (-(c₁ - c₂)⁻¹) * R₂) = -((c₁ : ℂ) - c₂)⁻¹ * aeval u R₂ := by
      simp only [map_mul, aeval_C, am]; push_cast; ring
    rw [hpc, hpc]
    apply span5_congr
    · convert mem_H0 hu0 ((natDegree_C_mul_le ((c₁ - c₂)⁻¹) R₁).trans hR₁) using 1
      rw [hS1]; exact shift₁ hD1 hd
    · convert mem_H0 hu0 ((natDegree_C_mul_le (-(c₁ - c₂)⁻¹) R₂).trans hR₂) using 1
      rw [hS2]; exact shift₂ hD2 hd
  · -- cyclic branch: D2b
    right; right
    obtain ⟨hcop', hdeg'⟩ := DiazModulus.coprime_pencil_mobius P Q hcop hdeg 1 (-c) 0 1 (by simp)
    simp only [map_zero, zero_mul, zero_add, map_one, one_mul] at hcop' hdeg'
    refine ⟨P + C (-c) * Q, Q, R₀, R₁, hcop', hdeg', hR₀, hR₁, ?_⟩
    rw [hpc]; exact hWeq
