-- Prove2me | solution 1 for CaiCandesShen.GeneralConvex.subgradient_strongly_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:17:34.10815+00:00
-- url     : https://prove2.me/submissions/74f88460-5ca2-4928-bffa-438775701f51

import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Basic

namespace CaiCandesShen.GeneralConvex

open Module InnerProductSpace

section nuc
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable abbrev aux_ssm_b (T : E →ₗ[ℝ] F) : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

lemma aux_ssm_inner (T : E →ₗ[ℝ] F) (i j : Fin (finrank ℝ E)) :
    ⟪T (aux_ssm_b T i), T (aux_ssm_b T j)⟫_ℝ =
      T.isSymmetric_adjoint_comp_self.eigenvalues rfl j * ⟪aux_ssm_b T i, aux_ssm_b T j⟫_ℝ := by
  rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply,
    LinearMap.IsSymmetric.apply_eigenvectorBasis, real_inner_smul_right]
  simp

lemma aux_ssm_sum_eq (T : E →ₗ[ℝ] F) :
    T.singularValues.sum (fun _ s => s) = ∑ i : Fin (finrank ℝ E), ‖T (aux_ssm_b T i)‖ := by
  rw [LinearMap.singularValues, Finsupp.sum_embDomain, Finsupp.sum_fintype _ _ (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finsupp.ofSupportFinite_coe]
  have h1 : ‖T (aux_ssm_b T i)‖ ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues rfl i := by
    rw [← real_inner_self_eq_norm_sq, aux_ssm_inner, real_inner_self_eq_norm_sq,
      (aux_ssm_b T).orthonormal.1 i]
    simp
  rw [← h1, Real.sqrt_sq (norm_nonneg _)]

omit [FiniteDimensional ℝ F] in
lemma aux_ssm_normsq {ι : Type*} [Fintype ι] (u : ι → F)
    (hu : Pairwise fun i j => ⟪u i, u j⟫_ℝ = 0) (hu1 : ∀ i, ‖u i‖ ≤ 1) (c : ι → ℝ) :
    ‖∑ i, c i • u i‖ ^ 2 ≤ ∑ i, c i * c i := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have h0 : ‖u i‖ ^ 2 ≤ 1 := by
      have := hu1 i
      have := norm_nonneg (u i)
      nlinarith
    have := mul_self_nonneg (c i)
    nlinarith
  · intro k _ hk
    rw [real_inner_smul_left, real_inner_smul_right, hu (Ne.symm hk)]
    simp
  · simp

lemma aux_ssm_le (T : E →ₗ[ℝ] F) {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E) (u : ι → F)
    (hu : Pairwise fun i j => ⟪u i, u j⟫_ℝ = 0) (hu1 : ∀ i, ‖u i‖ ≤ 1) :
    ∑ i, ⟪T (e i), u i⟫_ℝ ≤ T.singularValues.sum (fun _ s => s) := by
  rw [aux_ssm_sum_eq]
  set b := aux_ssm_b T
  have key : ∀ i, T (e i) = ∑ j, ⟪b j, e i⟫_ℝ • T (b j) := by
    intro i
    conv_lhs => rw [← b.sum_repr' (e i)]
    simp [map_sum, map_smul]
  have h2 : ∑ i, ⟪T (e i), u i⟫_ℝ = ∑ j, ⟪T (b j), ∑ i, ⟪b j, e i⟫_ℝ • u i⟫_ℝ := by
    simp_rw [key, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    rw [Finset.sum_comm]
  rw [h2]
  refine Finset.sum_le_sum fun j _ => ?_
  refine (real_inner_le_norm _ _).trans ?_
  have hw : ‖∑ i, ⟪b j, e i⟫_ℝ • u i‖ ≤ 1 := by
    have h3 := aux_ssm_normsq u hu hu1 (fun i => ⟪b j, e i⟫_ℝ)
    have h4 : ∑ i, ⟪b j, e i⟫_ℝ * ⟪b j, e i⟫_ℝ = 1 := by
      have := e.sum_inner_mul_inner (b j) (b j)
      simp_rw [real_inner_comm (b j) (e _)] at this
      rw [this, real_inner_self_eq_norm_sq, b.orthonormal.1 j]
      simp
    rw [h4] at h3
    have := norm_nonneg (∑ i, ⟪b j, e i⟫_ℝ • u i)
    nlinarith
  calc _ ≤ ‖T (b j)‖ * 1 := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = _ := mul_one _

lemma aux_ssm_eq (T : E →ₗ[ℝ] F) :
    T.singularValues.sum (fun _ s => s) =
      ∑ i, ⟪T (aux_ssm_b T i), ‖T (aux_ssm_b T i)‖⁻¹ • T (aux_ssm_b T i)⟫_ℝ := by
  rw [aux_ssm_sum_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  rcases eq_or_ne ‖T (aux_ssm_b T i)‖ 0 with h | h
  · simp [h]
  · field_simp

lemma aux_ssm_orth (T : E →ₗ[ℝ] F) :
    Pairwise fun i j => ⟪‖T (aux_ssm_b T i)‖⁻¹ • T (aux_ssm_b T i),
      ‖T (aux_ssm_b T j)‖⁻¹ • T (aux_ssm_b T j)⟫_ℝ = 0 := by
  intro i j hij
  rw [real_inner_smul_left, real_inner_smul_right, aux_ssm_inner,
    (aux_ssm_b T).orthonormal.2 hij]
  simp

omit [FiniteDimensional ℝ F] in
lemma aux_ssm_norm_le (x : F) : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with h | h
  · simp [h]
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

lemma aux_ssm_convex (A B : E →ₗ[ℝ] F) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (a • A + c • B).singularValues.sum (fun _ s => s) ≤
      a * A.singularValues.sum (fun _ s => s) + c * B.singularValues.sum (fun _ s => s) := by
  rw [aux_ssm_eq (a • A + c • B)]
  have hA := aux_ssm_le A (aux_ssm_b (a • A + c • B)) _ (aux_ssm_orth (a • A + c • B))
    (fun _ => aux_ssm_norm_le _)
  have hB := aux_ssm_le B (aux_ssm_b (a • A + c • B)) _ (aux_ssm_orth (a • A + c • B))
    (fun _ => aux_ssm_norm_le _)
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, real_inner_smul_left,
    Finset.sum_add_distrib, ← Finset.mul_sum] at hA hB ⊢
  nlinarith [mul_le_mul_of_nonneg_left hA ha, mul_le_mul_of_nonneg_left hB hc]

end nuc
section mat

lemma aux_ssm_nuc_convex {n₁ n₂ : ℕ} (X Y : Mat n₁ n₂) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    nuclearNorm (a • X + c • Y) ≤ a * nuclearNorm X + c * nuclearNorm Y := by
  unfold nuclearNorm
  rw [map_add, map_smul, map_smul]
  exact aux_ssm_convex _ _ a c ha hc

lemma aux_ssm_fI_add_left {n₁ n₂ : ℕ} (X Y W : Mat n₁ n₂) :
    frobInner (X + Y) W = frobInner X W + frobInner Y W := by
  simp [frobInner, add_mul, Finset.sum_add_distrib]

lemma aux_ssm_fI_sub_left {n₁ n₂ : ℕ} (X Y W : Mat n₁ n₂) :
    frobInner (X - Y) W = frobInner X W - frobInner Y W := by
  simp [frobInner, sub_mul, Finset.sum_sub_distrib]

lemma aux_ssm_fI_smul_left {n₁ n₂ : ℕ} (a : ℝ) (X W : Mat n₁ n₂) :
    frobInner (a • X) W = a * frobInner X W := by
  simp [frobInner, Finset.mul_sum, mul_assoc]

lemma aux_ssm_fI_comm {n₁ n₂ : ℕ} (X W : Mat n₁ n₂) :
    frobInner X W = frobInner W X := by
  simp [frobInner, mul_comm]

lemma aux_ssm_fI_add_right {n₁ n₂ : ℕ} (X Y W : Mat n₁ n₂) :
    frobInner W (X + Y) = frobInner W X + frobInner W Y := by
  rw [aux_ssm_fI_comm, aux_ssm_fI_add_left, aux_ssm_fI_comm X, aux_ssm_fI_comm Y]

lemma aux_ssm_fI_smul_right {n₁ n₂ : ℕ} (a : ℝ) (X W : Mat n₁ n₂) :
    frobInner W (a • X) = a * frobInner W X := by
  rw [aux_ssm_fI_comm, aux_ssm_fI_smul_left, aux_ssm_fI_comm]

lemma aux_ssm_fI_neg_right {n₁ n₂ : ℕ} (X W : Mat n₁ n₂) :
    frobInner W (-X) = - frobInner W X := by
  rw [← neg_one_smul ℝ X, aux_ssm_fI_smul_right]; ring

lemma aux_ssm_fI_self_nonneg {n₁ n₂ : ℕ} (X : Mat n₁ n₂) : 0 ≤ frobInner X X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

lemma aux_ssm_frobNorm_sq {n₁ n₂ : ℕ} (X : Mat n₁ n₂) : frobNorm X ^ 2 = frobInner X X :=
  Real.sq_sqrt (aux_ssm_fI_self_nonneg X)

lemma aux_ssm_lim {a b c : ℝ} (hc : 0 ≤ c) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → a ≤ b + t * c) :
    a ≤ b := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have ht : 0 < min 1 (ε / (c + 1)) := lt_min one_pos (div_pos hε (by linarith))
  have h1 := h _ ht (min_le_left _ _)
  have h2 : min 1 (ε / (c + 1)) * c ≤ ε := by
    calc min 1 (ε / (c + 1)) * c ≤ ε / (c + 1) * c :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hc
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  linarith

lemma aux_ssm_step {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ) (X Z D : Mat n₁ n₂)
    (hZ : IsSubgradient (fτ τ) X Z) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    frobInner Z D - frobInner X D ≤
      τ * (nuclearNorm (X + D) - nuclearNorm X) + t * (1 / 2 * frobInner D D) := by
  have h := hZ (X + t • D)
  have hXD : X + t • D - X = t • D := by abel
  have hcv : X + t • D = (1 - t) • X + t • (X + D) := by
    rw [sub_smul, one_smul, smul_add]; abel
  have hN := aux_ssm_nuc_convex X (X + D) (1 - t) t (by linarith) ht0.le
  rw [← hcv] at hN
  rw [hXD] at h
  simp only [fτ, aux_ssm_frobNorm_sq, aux_ssm_fI_smul_right, aux_ssm_fI_add_left,
    aux_ssm_fI_add_right, aux_ssm_fI_smul_left] at h
  rw [aux_ssm_fI_comm D X] at h
  have hmain : t * (frobInner Z D - frobInner X D) ≤
      t * (τ * (nuclearNorm (X + D) - nuclearNorm X) + t * (1 / 2 * frobInner D D)) := by
    nlinarith [mul_le_mul_of_nonneg_left hN hτ.le]
  exact le_of_mul_le_mul_left hmain ht0

lemma aux_ssm_sub {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ) (X Z D : Mat n₁ n₂)
    (hZ : IsSubgradient (fτ τ) X Z) :
    frobInner Z D - frobInner X D ≤ τ * (nuclearNorm (X + D) - nuclearNorm X) :=
  aux_ssm_lim (by have := aux_ssm_fI_self_nonneg D; positivity)
    (fun t ht0 ht1 => aux_ssm_step τ hτ X Z D hZ t ht0 ht1)

end mat

end CaiCandesShen.GeneralConvex

open CaiCandesShen.GeneralConvex

theorem solution {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (X X' Z Z' : Mat n₁ n₂) (hZ : IsSubgradient (fτ τ) X Z) (hZ' : IsSubgradient (fτ τ) X' Z') :
    frobNorm (X - X') ^ 2 ≤ frobInner (Z - Z') (X - X') := by
  have h1 := aux_ssm_sub τ hτ X Z (X' - X) hZ
  have h2 := aux_ssm_sub τ hτ X' Z' (X - X') hZ'
  have e1 : X + (X' - X) = X' := by abel
  have e2 : X' + (X - X') = X := by abel
  have e3 : X' - X = -(X - X') := by abel
  rw [e1] at h1
  rw [e2] at h2
  rw [e3, aux_ssm_fI_neg_right, aux_ssm_fI_neg_right] at h1
  rw [aux_ssm_frobNorm_sq, aux_ssm_fI_sub_left, aux_ssm_fI_sub_left]
  linarith
