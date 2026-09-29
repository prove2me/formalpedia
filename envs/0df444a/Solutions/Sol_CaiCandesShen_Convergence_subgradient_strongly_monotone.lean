-- Prove2me | solution 1 for CaiCandesShen.Convergence.subgradient_strongly_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:49:29.693993+00:00
-- url     : https://prove2.me/submissions/4c6eab1e-fd1d-4300-87c7-1d0b0e7d2cac

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic

namespace CaiCandesShen.Convergence

open Module InnerProductSpace

section aux_ssm_sec

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The eigenbasis of `T* T`. -/
noncomputable abbrev aux_ssm_b (T : E →ₗ[ℝ] F) : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

lemma aux_ssm_inner_img (T : E →ₗ[ℝ] F) (i j : Fin (finrank ℝ E)) :
    inner ℝ (T (aux_ssm_b T i)) (T (aux_ssm_b T j)) =
      T.isSymmetric_adjoint_comp_self.eigenvalues rfl i *
        inner ℝ (aux_ssm_b T i) (aux_ssm_b T j) := by
  rw [← LinearMap.adjoint_inner_left]
  have h := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  rw [LinearMap.comp_apply] at h
  rw [aux_ssm_b, h, real_inner_smul_left]
  simp

lemma aux_ssm_nu_eq (T : E →ₗ[ℝ] F) :
    T.singularValues.sum (fun _ s => s) = ∑ i, ‖T (aux_ssm_b T i)‖ := by
  rw [Finsupp.sum_of_support_subset T.singularValues (s := Finset.range (finrank ℝ E)) ?_ _
    (fun _ _ => rfl)]
  · rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [T.singularValues_fin rfl i]
    have h := aux_ssm_inner_img T i i
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      (aux_ssm_b T).orthonormal.1 i, one_pow, mul_one] at h
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  · intro i hi
    rw [Finset.mem_range]
    by_contra h
    exact (Finsupp.mem_support_iff.mp hi) (T.singularValues_of_finrank_le (not_lt.mp h))

lemma aux_ssm_upper (T U : E →ₗ[ℝ] F) (hU : ∀ v, ‖U v‖ ≤ ‖v‖) :
    LinearMap.trace ℝ E (LinearMap.adjoint U ∘ₗ T) ≤ T.singularValues.sum (fun _ s => s) := by
  rw [aux_ssm_nu_eq, LinearMap.trace_eq_sum_inner _ (aux_ssm_b T)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  calc inner ℝ (U (aux_ssm_b T i)) (T (aux_ssm_b T i))
      ≤ ‖U (aux_ssm_b T i)‖ * ‖T (aux_ssm_b T i)‖ := real_inner_le_norm _ _
    _ ≤ 1 * ‖T (aux_ssm_b T i)‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc _ ≤ ‖aux_ssm_b T i‖ := hU _
          _ = 1 := (aux_ssm_b T).orthonormal.1 i
    _ = _ := one_mul _

lemma aux_ssm_exists (M : E →ₗ[ℝ] F) : ∃ U : E →ₗ[ℝ] F, (∀ v, ‖U v‖ ≤ ‖v‖) ∧
    LinearMap.trace ℝ E (LinearMap.adjoint U ∘ₗ M) = M.singularValues.sum (fun _ s => s) := by
  set e := aux_ssm_b M with he
  set u : Fin (finrank ℝ E) → F := fun i => ‖M (e i)‖⁻¹ • M (e i) with hu
  have hUe : ∀ i, e.toBasis.constr ℝ u (e i) = u i := by
    intro i
    have := e.toBasis.constr_basis ℝ u i
    rwa [OrthonormalBasis.coe_toBasis] at this
  refine ⟨e.toBasis.constr ℝ u, ?_, ?_⟩
  · intro v
    have hUv : e.toBasis.constr ℝ u v = ∑ i, inner ℝ (e i) v • u i := by
      conv_lhs => rw [← e.sum_repr' v]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hUe]
    have horth : ∀ i j, i ≠ j → inner ℝ (u i) (u j) = 0 := by
      intro i j hij
      rw [hu]
      simp only
      rw [real_inner_smul_left, real_inner_smul_right, he, aux_ssm_inner_img M i j,
        (aux_ssm_b M).orthonormal.2 hij]
      simp
    have hnorm : ∀ i, ‖u i‖ ≤ 1 := by
      intro i
      rw [hu]
      simp only
      rw [norm_smul, norm_inv, norm_norm]
      by_cases h0 : ‖M (e i)‖ = 0
      · rw [h0]; simp
      · rw [inv_mul_cancel₀ h0]
    have hsq : ‖e.toBasis.constr ℝ u v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [hUv, ← real_inner_self_eq_norm_sq, sum_inner, ← e.sum_sq_inner_right v]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [inner_sum, Finset.sum_eq_single i]
      · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
        have h1 := hnorm i
        have h2 : ‖u i‖ ^ 2 ≤ 1 := by
          have := norm_nonneg (u i)
          nlinarith
        have h3 := sq_nonneg (inner ℝ (e i) v)
        nlinarith
      · intro j _ hji
        rw [real_inner_smul_left, real_inner_smul_right, horth i j (Ne.symm hji)]
        simp
      · intro h; exact absurd (Finset.mem_univ i) h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
  · rw [aux_ssm_nu_eq, ← he, LinearMap.trace_eq_sum_inner _ e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, hUe, hu]
    simp only
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    by_cases h0 : ‖M (e i)‖ = 0
    · rw [h0]; simp
    · field_simp

lemma aux_ssm_convex (S T : E →ₗ[ℝ] F) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a • S + b • T).singularValues.sum (fun _ s => s) ≤
      a * S.singularValues.sum (fun _ s => s) + b * T.singularValues.sum (fun _ s => s) := by
  obtain ⟨U, hU, heq⟩ := aux_ssm_exists (a • S + b • T)
  rw [← heq, LinearMap.comp_add, LinearMap.comp_smul, LinearMap.comp_smul, map_add, map_smul,
    map_smul, smul_eq_mul, smul_eq_mul]
  have h1 := aux_ssm_upper S U hU
  have h2 := aux_ssm_upper T U hU
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

end aux_ssm_sec

lemma aux_ssm_nuc_convex {n₁ n₂ : ℕ} (X Y : Mat n₁ n₂) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    nuclearNorm (a • X + b • Y) ≤ a * nuclearNorm X + b * nuclearNorm Y := by
  unfold nuclearNorm
  rw [map_add, map_smul, map_smul]
  exact aux_ssm_convex _ _ a b ha hb

lemma aux_ssm_fi_add_right {n₁ n₂ : ℕ} (A B C : Mat n₁ n₂) :
    frobInner A (B + C) = frobInner A B + frobInner A C := by
  unfold frobInner
  simp [mul_add, Finset.sum_add_distrib]

lemma aux_ssm_fi_sub_right {n₁ n₂ : ℕ} (A B C : Mat n₁ n₂) :
    frobInner A (B - C) = frobInner A B - frobInner A C := by
  unfold frobInner
  simp [mul_sub, Finset.sum_sub_distrib]

lemma aux_ssm_fi_sub_left {n₁ n₂ : ℕ} (A B C : Mat n₁ n₂) :
    frobInner (A - B) C = frobInner A C - frobInner B C := by
  unfold frobInner
  simp [sub_mul, Finset.sum_sub_distrib]

lemma aux_ssm_fi_add_left {n₁ n₂ : ℕ} (A B C : Mat n₁ n₂) :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  unfold frobInner
  simp [add_mul, Finset.sum_add_distrib]

lemma aux_ssm_fi_smul_right {n₁ n₂ : ℕ} (A B : Mat n₁ n₂) (t : ℝ) :
    frobInner A (t • B) = t * frobInner A B := by
  unfold frobInner
  simp [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma aux_ssm_fi_smul_left {n₁ n₂ : ℕ} (A B : Mat n₁ n₂) (t : ℝ) :
    frobInner (t • A) B = t * frobInner A B := by
  unfold frobInner
  simp [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma aux_ssm_fi_comm {n₁ n₂ : ℕ} (A B : Mat n₁ n₂) : frobInner A B = frobInner B A := by
  unfold frobInner
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma aux_ssm_fi_self_nonneg {n₁ n₂ : ℕ} (A : Mat n₁ n₂) : 0 ≤ frobInner A A := by
  unfold frobInner
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

lemma aux_ssm_fn_sq {n₁ n₂ : ℕ} (A : Mat n₁ n₂) : frobNorm A ^ 2 = frobInner A A := by
  unfold frobNorm
  exact Real.sq_sqrt (aux_ssm_fi_self_nonneg A)

/-- Key one-sided inequality: `⟨Z - X, X' - X⟩ ≤ τ (‖X'‖_* - ‖X‖_*)`. -/
lemma aux_ssm_key {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ) (X X' Z : Mat n₁ n₂)
    (hZ : IsSubgradient (fτ τ) X Z) :
    frobInner Z (X' - X) - frobInner X (X' - X) ≤ τ * (nuclearNorm X' - nuclearNorm X) := by
  set D := X' - X with hD
  set c := frobInner D D with hc
  have hc0 : 0 ≤ c := aux_ssm_fi_self_nonneg D
  have ht : ∀ t : ℝ, 0 < t → t ≤ 1 →
      frobInner Z D - frobInner X D ≤ τ * (nuclearNorm X' - nuclearNorm X) + t / 2 * c := by
    intro t ht0 ht1
    have h := hZ (X + t • D)
    have hW : X + t • D = (1 - t) • X + t • X' := by
      rw [hD, smul_sub, sub_smul, one_smul]; abel
    have hN := aux_ssm_nuc_convex X X' (1 - t) t (by linarith) ht0.le
    rw [← hW] at hN
    unfold fτ at h
    rw [add_sub_cancel_left, aux_ssm_fn_sq, aux_ssm_fn_sq, aux_ssm_fi_smul_right,
      aux_ssm_fi_add_left, aux_ssm_fi_add_right, aux_ssm_fi_add_right, aux_ssm_fi_smul_left,
      aux_ssm_fi_smul_right, aux_ssm_fi_smul_left, aux_ssm_fi_smul_right,
      aux_ssm_fi_comm D X] at h
    have h2 : t * (frobInner Z D - frobInner X D) ≤
        t * (τ * (nuclearNorm X' - nuclearNorm X) + t / 2 * c) := by
      nlinarith [mul_le_mul_of_nonneg_left hN hτ.le]
    exact le_of_mul_le_mul_left h2 ht0
  apply le_of_forall_pos_le_add
  intro ε hε
  set t := min 1 (ε / (c + 1)) with htdef
  have ht0 : 0 < t := lt_min one_pos (div_pos hε (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htc : t / 2 * c ≤ ε := by
    have h1 : t ≤ ε / (c + 1) := min_le_right _ _
    have h2 : t * (c + 1) ≤ ε := by
      rw [le_div_iff₀ (by linarith)] at h1; exact h1
    nlinarith
  linarith [ht t ht0 ht1]

theorem aux_ssm_main {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (X X' Z Z' : Mat n₁ n₂) (hZ : IsSubgradient (fτ τ) X Z) (hZ' : IsSubgradient (fτ τ) X' Z') :
    frobNorm (X - X') ^ 2 ≤ frobInner (Z - Z') (X - X') := by
  have h1 := aux_ssm_key τ hτ X X' Z hZ
  have h2 := aux_ssm_key τ hτ X' X Z' hZ'
  have hneg : ∀ A : Mat n₁ n₂, frobInner A (X' - X) = - frobInner A (X - X') := by
    intro A
    rw [aux_ssm_fi_sub_right, aux_ssm_fi_sub_right]; ring
  rw [hneg, hneg] at h1
  rw [aux_ssm_fn_sq, aux_ssm_fi_sub_left, aux_ssm_fi_sub_left]
  linarith

end CaiCandesShen.Convergence

open CaiCandesShen.Convergence

theorem solution {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (X X' Z Z' : Mat n₁ n₂) (hZ : IsSubgradient (fτ τ) X Z) (hZ' : IsSubgradient (fτ τ) X' Z') :
    frobNorm (X - X') ^ 2 ≤ frobInner (Z - Z') (X - X') :=
  aux_ssm_main τ hτ X X' Z Z' hZ hZ'
