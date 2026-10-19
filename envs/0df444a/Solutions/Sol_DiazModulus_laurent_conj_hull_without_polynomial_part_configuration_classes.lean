-- Prove2me | solution 1 for DiazModulus.laurent_conj_hull_without_polynomial_part_configuration_classes
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:43:45.556106+00:00
-- url     : https://prove2.me/submissions/00b573e5-6ca9-4798-86ca-20cbdc7bee92

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_conj_hull_shifted_polynomial_model
import Theorems.Thm_DiazModulus_config_shifted_coprime_polynomial_factors
import Theorems.Thm_DiazModulus_two_by_three_configuration_ratio_degree_le_two
import Theorems.Thm_DiazModulus_coprime_pencil_of_degree_le_two_normal_form
import Theorems.Thm_DiazModulus_laurent_window_quadratic_pencils_carry_no_three_factors
import Theorems.Thm_DiazModulus_laurent_window_degree_one_pencil_factor_space
import Theorems.Thm_DiazModulus_laurent_window_involution_pencil_normal_form
import Theorems.Thm_DiazModulus_laurent_degree_one_conj_stable_space_real_pencil_normal_form
import Theorems.Thm_DiazModulus_laurent_involution_space_conj_stable_constraints

open Complex ComplexConjugate

/-! # Without `v² P(v)`, a configuration puts the Laurent hull in class (Q) or (R)

Let `W = span(1, v, v̄, z, z̄)` with `z` a Laurent polynomial in `v`, `v v̄ = 1`, `dim W = 5`, and no
non-zero `v² P(v)` in `W`. The shifted polynomial model (`laurent_conj_hull_shifted_polynomial_model`)
writes `W` as the image of `H_N ⊔ M` under the `Q̄`-linear map `Φ : F ↦ F(v)/v^N`, with `M` two-sided.
A configuration `x ⊗ y` in `W` factors (`config_shifted_coprime_polynomial_factors`) through coprime
`a₀, a₁` and free `b₀, b₁, b₂` with `aᵢ bⱼ ∈ H_N ⊔ M` and `x₁ a₀(v) = x₀ a₁(v)`; the freeness of `x`
makes the ratio non-constant, `two_by_three_configuration_ratio_degree_le_two` bounds its degree by
two, and `coprime_pencil_of_degree_le_two_normal_form` lists the four pencils. The pencils
`(1, X² + αX)` and `(X + β, X² + γX)` carry no three free factors
(`laurent_window_quadratic_pencils_carry_no_three_factors`). For `(1, X)`,
`laurent_window_degree_one_pencil_factor_space` gives `G₀` with `W = span(1, v, v̄, g, vg)`, `g = Φ G₀`;
conjugation-stability of `W` and the factor-space property give `ḡ ∈ span(1, v, vg)`, and
`laurent_degree_one_conj_stable_space_real_pencil_normal_form` gives class (R), `v² ∉ W` excluding
`deg G ≤ 1`. For `(X, X² + β)`, `laurent_window_involution_pencil_normal_form` puts `M` in the involution
normal form, `Φ` carries it to `span(1, v, v̄, v̄² + e v², β v̄³ + ζ v² + e v³)`, and
`laurent_involution_space_conj_stable_constraints` gives the constraints of class (Q). -/

namespace R18_M2

open DiazModulus Polynomial

theorem conj_mem {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar :=
  mem_Qbar_iff.2 ((mem_Qbar_iff.1 ha).algHom
    ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ))

/-- A span whose generators have conjugates in it is conjugation-stable. -/
theorem span_conj_stable {S : Set ℂ} (hS : ∀ x ∈ S, conj x ∈ Submodule.span Qbar S) :
    ∀ w ∈ Submodule.span Qbar S, conj w ∈ Submodule.span Qbar S := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have hcx : conj (c • x) = (⟨conj (c : ℂ), conj_mem c.2⟩ : ↥Qbar) • conj x :=
      map_mul conj (c : ℂ) x
    rw [hcx]
    exact Submodule.smul_mem _ _ hx

/-- The shifted evaluation `F ↦ F(v)/v^N`, as a `Q̄`-linear map. -/
noncomputable def Φ (v : ℂ) (N : ℕ) : (↥Qbar)[X] →ₗ[↥Qbar] ℂ where
  toFun F := aeval v F / v ^ N
  map_add' F G := by rw [map_add, add_div]
  map_smul' r F := by rw [map_smul, RingHom.id_apply, smul_div_assoc]

theorem Φ_apply (v : ℂ) (N : ℕ) (F : (↥Qbar)[X]) : Φ v N F = aeval v F / v ^ N := rfl

theorem Φ_X_mul (v : ℂ) (N : ℕ) (F : (↥Qbar)[X]) : Φ v N (X * F) = v * Φ v N F := by
  simp only [Φ_apply, map_mul, aeval_X, mul_div_assoc]

theorem Φ_C_mul (v : ℂ) (N : ℕ) (a : ↥Qbar) (F : (↥Qbar)[X]) :
    Φ v N (C a * F) = (a : ℂ) * Φ v N F := by
  simp only [Φ_apply, map_mul, aeval_C, mul_div_assoc]; rfl

theorem Φ_low {v : ℂ} (hv0 : v ≠ 0) (hcv : conj v = v⁻¹) {N d : ℕ} (hd : d ≤ N) :
    Φ v N (X ^ (N - d)) = conj v ^ d := by
  rw [Φ_apply, aeval_X_pow, pow_sub₀ v hv0 hd, hcv, inv_pow]
  field_simp

theorem Φ_high {v : ℂ} (hv0 : v ≠ 0) (N d : ℕ) : Φ v N (X ^ (N + d)) = v ^ d := by
  rw [Φ_apply, aeval_X_pow, pow_add]; field_simp

theorem Φ_N {v : ℂ} (hv0 : v ≠ 0) (N : ℕ) : Φ v N (X ^ N) = 1 := by
  rw [Φ_apply, aeval_X_pow, div_self (pow_ne_zero _ hv0)]

theorem Φ_pred {v : ℂ} (hv0 : v ≠ 0) (hcv : conj v = v⁻¹) {N : ℕ} (hN : 1 ≤ N) :
    Φ v N (X ^ (N - 1)) = conj v := by
  rw [Φ_low hv0 hcv hN, pow_one]

theorem Φ_succ {v : ℂ} (hv0 : v ≠ 0) (N : ℕ) : Φ v N (X ^ (N + 1)) = v := by
  rw [Φ_high hv0, pow_one]

/-- The image of a window span `span(X^(N-1), X^N, X^(N+1), A, B)`. -/
theorem map5 {v : ℂ} (hv0 : v ≠ 0) (hcv : conj v = v⁻¹) {N : ℕ} (hN : 1 ≤ N) (A B : (↥Qbar)[X]) :
    Submodule.map (Φ v N)
        (Submodule.span (↥Qbar) ({X ^ (N - 1), X ^ N, X ^ (N + 1), A, B} : Set (↥Qbar)[X])) =
      Submodule.span (↥Qbar) ({1, v, conj v, Φ v N A, Φ v N B} : Set ℂ) := by
  rw [Submodule.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, Φ_pred hv0 hcv hN, Φ_N hv0, Φ_succ hv0]
  rw [Set.insert_comm (conj v) 1, Set.insert_comm (conj v) v]

theorem Φ_n0 {v : ℂ} (hv0 : v ≠ 0) (hcv : conj v = v⁻¹) {N : ℕ} (hN : 2 ≤ N) (e : ↥Qbar) :
    Φ v N (X ^ (N - 2) + C e * X ^ (N + 2)) = conj v ^ 2 + (e : ℂ) * v ^ 2 := by
  rw [map_add, Φ_C_mul, Φ_low hv0 hcv hN, Φ_high hv0]

theorem Φ_n1 {v : ℂ} (hv0 : v ≠ 0) (hcv : conj v = v⁻¹) {N : ℕ} (hN : 3 ≤ N) (β ζ e : ↥Qbar) :
    Φ v N (C β * X ^ (N - 3) + C ζ * X ^ (N + 2) + C e * X ^ (N + 3)) =
      (β : ℂ) * conj v ^ 3 + (ζ : ℂ) * v ^ 2 + (e : ℂ) * v ^ 3 := by
  rw [map_add, map_add, Φ_C_mul, Φ_C_mul, Φ_C_mul, Φ_low hv0 hcv hN, Φ_high hv0, Φ_high hv0]

/-- A free pair `x` admits no relation `x₁ α = x₀ β` with `α, β` not both zero. -/
theorem pair_free {x : Fin 2 → ℂ} (hx : LinearIndependent (↥Qbar) x) {α β : ↥Qbar}
    (h : x 1 * (α : ℂ) = x 0 * (β : ℂ)) : α = 0 ∧ β = 0 := by
  have := Fintype.linearIndependent_iff.1 hx ![β, -α] (by
    simp [Fin.sum_univ_two, Subfield.smul_def]
    linear_combination -h)
  exact ⟨by simpa using this 1, by simpa using this 0⟩

theorem range5 (a b c d e : ℂ) : Set.range ![a, b, c, d, e] = ({a, b, c, d, e} : Set ℂ) := by
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons,
    Matrix.range_cons_empty]
  simp only [Set.singleton_union]

end R18_M2

open DiazModulus R18_M2 Polynomial in
theorem solution
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1) (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ)) = 5)
    (hB : ∀ P : Polynomial ↥Qbar, v ^ 2 * Polynomial.aeval v P ∈ Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ) → P = 0)
    (hconf : ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ)) :
    (∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, v, conj v, conj v ^ 2 + e * v ^ 2, β * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3} : Set ℂ)) ∨
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, v, conj v, Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G), conj (Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G))} : Set ℂ)) := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ Qbar.zero_mem)
  have hcv : conj v = v⁻¹ := eq_inv_of_mul_eq_one_right hv1
  obtain ⟨N, M, hN3, hM2, hMc, hMo, hMd, hiff, honto⟩ :=
    DiazModulus.laurent_conj_hull_shifted_polynomial_model v hv hv1 k c hc h5 hB
  obtain ⟨x, y, hx, hy, hxy⟩ := hconf
  set Z := ∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j with hZ
  set W := Submodule.span Qbar ({1, v, conj v, Z, conj Z} : Set ℂ) with hW
  set HM := Submodule.span (↥Qbar) ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set (↥Qbar)[X]) ⊔ M
    with hHM
  have m1 : (1 : ℂ) ∈ W := Submodule.subset_span (by simp)
  have mv : v ∈ W := Submodule.subset_span (by simp)
  have mcv : conj v ∈ W := Submodule.subset_span (by simp)
  have hWc : ∀ w ∈ W, conj w ∈ W := span_conj_stable (by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with h | h | h | h | h <;> rw [h]
    · rw [map_one]; exact m1
    · exact mcv
    · rw [Complex.conj_conj]; exact mv
    · exact Submodule.subset_span (by simp)
    · rw [Complex.conj_conj]; exact Submodule.subset_span (by simp))
  have hWmap : W = Submodule.map (Φ v N) HM := by
    ext w
    constructor
    · intro hw
      obtain ⟨F, hF, hFe⟩ := honto w hw
      exact Submodule.mem_map.2 ⟨F, hF, hFe⟩
    · intro hw
      obtain ⟨F, hF, rfl⟩ := Submodule.mem_map.1 hw
      exact (hiff F).2 hF
  -- coprime factors (C1)
  obtain ⟨a, b, hcop, hb, hab, hxa⟩ :=
    DiazModulus.config_shifted_coprime_polynomial_factors hv HM N x y hx hy (fun i j => by
      obtain ⟨F, hF, hFe⟩ := honto _ (hxy i j)
      refine ⟨F, hF, ?_⟩
      rw [div_eq_iff (pow_ne_zero N hv0)] at hFe
      rw [hFe, mul_comm])
  -- the ratio is not constant
  have hdeg1 : 1 ≤ max (a 0).natDegree (a 1).natDegree := by
    by_contra hlt
    have h0 : (a 0).natDegree = 0 := by omega
    have h1 : (a 1).natDegree = 0 := by omega
    rw [eq_C_of_natDegree_eq_zero h0, eq_C_of_natDegree_eq_zero h1, aeval_C, aeval_C] at hxa
    obtain ⟨hα, hβ⟩ := pair_free hx hxa
    rw [eq_C_of_natDegree_eq_zero h0, eq_C_of_natDegree_eq_zero h1, hα, hβ, map_zero] at hcop
    exact not_isCoprime_zero_zero hcop
  -- the ratio has degree at most two (C2)
  have : FiniteDimensional (↥Qbar) W := Module.finite_of_finrank_pos (by rw [h5]; norm_num)
  have hdeg2 := DiazModulus.two_by_three_configuration_ratio_degree_le_two v hv W h5.le m1 mv
    (by rw [← hcv]; exact mcv) x y hx hy hxy (a 1) (a 0) hcop.symm (by rwa [max_comm]) hxa
  -- the four pencils (L1)
  obtain ⟨p, q, hpq, hcases⟩ := DiazModulus.coprime_pencil_of_degree_le_two_normal_form (↥Qbar)
    (a 0) (a 1) hcop hdeg1 (by rwa [max_comm])
  have hmul : ∀ r ∈ Submodule.span (↥Qbar) ({a 0, a 1} : Set (↥Qbar)[X]), ∀ j, r * b j ∈ HM := by
    intro r hr j
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hr
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
    exact HM.add_mem (HM.smul_mem _ (hab 0 j)) (HM.smul_mem _ (hab 1 j))
  have hpb : ∀ j, p * b j ∈ HM := hmul p (by rw [hpq]; exact Submodule.subset_span (by simp))
  have hqb : ∀ j, q * b j ∈ HM := hmul q (by rw [hpq]; exact Submodule.subset_span (by simp))
  have L3 := DiazModulus.laurent_window_quadratic_pencils_carry_no_three_factors (↥Qbar) N M hM2
    hMo hMd
  rcases hcases with ⟨rfl, rfl⟩ | ⟨α, rfl, rfl⟩ | ⟨β, hβ, rfl, rfl⟩ | ⟨β, γ, hβ, -, rfl, rfl⟩
  · -- the pencil `(1, X)`: class (R)
    right
    obtain ⟨G₀, hG₀W, hXG₀, hV1, hHMeq⟩ :=
      DiazModulus.laurent_window_degree_one_pencil_factor_space (↥Qbar) N M hM2 hMo hMd b hb
        (fun j => ⟨by rw [← one_mul (b j)]; exact hpb j, hqb j⟩)
    have hHMeq' : HM = Submodule.span (↥Qbar)
        ({X ^ (N - 1), X ^ N, X ^ (N + 1), G₀, X * G₀} : Set (↥Qbar)[X]) := hHMeq
    have hWg : W = Submodule.span Qbar
        ({1, v, conj v, aeval v G₀ / v ^ N, v * (aeval v G₀ / v ^ N)} : Set ℂ) := by
      rw [hWmap, hHMeq', map5 hv0 hcv (by omega), Φ_X_mul, Φ_apply]
    have hind : LinearIndependent (↥Qbar) ![1, v, conj v, aeval v G₀ / v ^ N,
        v * (aeval v G₀ / v ^ N)] := by
      rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, range5, ← hWg, h5]; rfl
    have hcg : conj (aeval v G₀ / v ^ N) ∈
        Submodule.span Qbar ({1, v, v * (aeval v G₀ / v ^ N)} : Set ℂ) := by
      have hvgW : v * (aeval v G₀ / v ^ N) ∈ W := by
        rw [← Φ_apply, ← Φ_X_mul]; exact (hiff _).2 hXG₀
      have hfW : conj v * conj (aeval v G₀ / v ^ N) ∈ W := by
        have := hWc _ hvgW; rwa [map_mul] at this
      obtain ⟨F, hF, hFf⟩ := honto _ hfW
      have hXF : X * F ∈ HM := (hiff (X * F)).1 (by
        rw [← Φ_apply, Φ_X_mul, Φ_apply, hFf, ← mul_assoc, hv1, one_mul]
        exact hWc _ ((hiff G₀).2 hG₀W))
      obtain ⟨a₁, a₂, a₃, hF'⟩ := Submodule.mem_span_triple.1 (hV1 F hF hXF)
      have hΦF := congrArg (Φ v N) hF'
      rw [map_add, map_add, map_smul, map_smul, map_smul, Φ_pred hv0 hcv (by omega), Φ_N hv0,
        Φ_apply, Φ_apply, hFf] at hΦF
      refine Submodule.mem_span_triple.2 ⟨a₁, a₂, a₃, ?_⟩
      simp only [Subfield.smul_def, smul_eq_mul] at hΦF ⊢
      linear_combination v * hΦF - (a₁ : ℂ) * hv1 + conj (aeval v G₀ / v ^ N) * hv1
    obtain ⟨κ, hκ, hκ1, G, hG0, hdeg, hspan⟩ :=
      DiazModulus.laurent_degree_one_conj_stable_space_real_pencil_normal_form v hv hv1 N G₀
        hind hcg
    have h2 : 2 ≤ G.natDegree := by
      rcases hdeg with h | h
      · exact h
      · exfalso
        have : v ^ 2 * aeval v (1 : (↥Qbar)[X]) ∈ W := by
          rw [map_one, mul_one, hWg]; exact h
        exact one_ne_zero (hB 1 this)
    exact ⟨κ, hκ, hκ1, G, hG0, h2, hWg.trans hspan⟩
  · -- the pencil `(1, X² + αX)`: none
    exact absurd ⟨b, hb, fun j => ⟨by rw [← one_mul (b j)]; exact hpb j, hqb j⟩⟩ (L3.1 α)
  · -- the pencil `(X, X² + β)`: class (Q)
    left
    obtain ⟨e, ζ, -, hMeq⟩ := DiazModulus.laurent_window_involution_pencil_normal_form (↥Qbar) N M
      hM2 hN3 hMc hMo hMd β hβ b hb (fun j => ⟨hpb j, hqb j⟩)
    have hHM5 : HM = Submodule.span (↥Qbar) ({X ^ (N - 1), X ^ N, X ^ (N + 1),
        X ^ (N - 2) + C e * X ^ (N + 2), C β * X ^ (N - 3) + C ζ * X ^ (N + 2) + C e * X ^ (N + 3)} :
          Set (↥Qbar)[X]) := by
      rw [hHM, hMeq, ← Submodule.span_union]
      congr 1
      simp only [Set.insert_union, Set.singleton_union]
    have hWQ : W = Submodule.span Qbar ({1, v, conj v, conj v ^ 2 + (e : ℂ) * v ^ 2,
        (β : ℂ) * conj v ^ 3 + (ζ : ℂ) * v ^ 2 + (e : ℂ) * v ^ 3} : Set ℂ) := by
      rw [hWmap, hHM5, map5 hv0 hcv (by omega), Φ_n0 hv0 hcv (by omega), Φ_n1 hv0 hcv hN3]
    obtain ⟨h1, h2, h3⟩ := DiazModulus.laurent_involution_space_conj_stable_constraints v hv hv1
      (e : ℂ) (β : ℂ) (ζ : ℂ) e.2 β.2 ζ.2 (fun h => hβ (Subtype.ext h))
      (by rw [← hWQ]; exact hWc)
    exact ⟨e, β, ζ, e.2, β.2, ζ.2, h1, h2, h3, hWQ⟩
  · -- the pencil `(X + β, X² + γX)`: none
    exact absurd ⟨b, hb, fun j => ⟨hpb j, hqb j⟩⟩ (L3.2 β γ hβ)
