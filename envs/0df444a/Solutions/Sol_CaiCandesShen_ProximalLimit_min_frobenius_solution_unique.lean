-- Prove2me | solution 1 for CaiCandesShen.ProximalLimit.min_frobenius_solution_unique
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:05:42.054923+00:00
-- url     : https://prove2.me/submissions/c655c78c-af09-44b1-85fe-ea31d8945142

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology

namespace CaiCandesShen.ProximalLimit

open scoped InnerProductSpace

section aux_mfs_section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Orthonormal eigenbasis of `T† T`. -/
noncomputable def aux_mfs_vb (T : E →ₗ[ℝ] F) :
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

lemma aux_mfs_inner_apply (T : E →ₗ[ℝ] F) (i j : Fin (Module.finrank ℝ E)) :
    ⟪T (aux_mfs_vb T i), T (aux_mfs_vb T j)⟫_ℝ =
      if i = j then T.isSymmetric_adjoint_comp_self.eigenvalues rfl i else 0 := by
  rw [← LinearMap.adjoint_inner_left]
  have h := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  rw [LinearMap.comp_apply] at h
  unfold aux_mfs_vb
  rw [h, real_inner_smul_left, OrthonormalBasis.inner_eq_ite]
  split_ifs <;> simp

lemma aux_mfs_orth (T : E →ₗ[ℝ] F) (i j : Fin (Module.finrank ℝ E)) :
    ⟪T (aux_mfs_vb T i), T (aux_mfs_vb T j)⟫_ℝ =
      if i = j then ‖T (aux_mfs_vb T i)‖ ^ 2 else 0 := by
  split_ifs with h
  · subst h; exact real_inner_self_eq_norm_sq _
  · rw [aux_mfs_inner_apply, if_neg h]

lemma aux_mfs_norm_apply (T : E →ₗ[ℝ] F) (i : Fin (Module.finrank ℝ E)) :
    ‖T (aux_mfs_vb T i)‖ = T.singularValues i := by
  rw [T.singularValues_fin rfl i, ← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    aux_mfs_inner_apply, if_pos rfl]

lemma aux_mfs_sum (T : E →ₗ[ℝ] F) :
    T.singularValues.sum (fun _ s => s) = ∑ i, ‖T (aux_mfs_vb T i)‖ := by
  simp_rw [aux_mfs_norm_apply]
  rw [Finsupp.sum_of_support_subset T.singularValues (s := Finset.range (Module.finrank ℝ E)) ?_
    (fun _ s => s) (fun _ _ => rfl)]
  · rw [Finset.sum_range]
  · intro i hi
    rw [Finsupp.mem_support_iff] at hi
    rw [Finset.mem_range]
    by_contra h
    exact hi (T.singularValues_of_finrank_le (not_lt.mp h))

lemma aux_mfs_trace {ι : Type*} [Fintype ι] (W T : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) :
    ∑ i, ⟪W (b i), T (b i)⟫_ℝ = LinearMap.trace ℝ E (LinearMap.adjoint T ∘ₗ W) := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  exact real_inner_comm _ _

lemma aux_mfs_upper {ι : Type*} [Fintype ι] (W T : E →ₗ[ℝ] F) (hW : ∀ x, ‖W x‖ ≤ ‖x‖)
    (b : OrthonormalBasis ι ℝ E) :
    ∑ i, ⟪W (b i), T (b i)⟫_ℝ ≤ T.singularValues.sum (fun _ s => s) := by
  rw [aux_mfs_trace, ← aux_mfs_trace W T (aux_mfs_vb T), aux_mfs_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ⟪W (aux_mfs_vb T i), T (aux_mfs_vb T i)⟫_ℝ
      ≤ ‖W (aux_mfs_vb T i)‖ * ‖T (aux_mfs_vb T i)‖ := real_inner_le_norm _ _
    _ ≤ 1 * ‖T (aux_mfs_vb T i)‖ := by
        gcongr
        simpa using hW (aux_mfs_vb T i)
    _ = _ := one_mul _

lemma aux_mfs_exists (C : E →ₗ[ℝ] F) :
    ∃ W : E →ₗ[ℝ] F, (∀ x, ‖W x‖ ≤ ‖x‖) ∧
      C.singularValues.sum (fun _ s => s) =
        ∑ i, ⟪W (aux_mfs_vb C i), C (aux_mfs_vb C i)⟫_ℝ := by
  let v := aux_mfs_vb C
  let σ : Fin (Module.finrank ℝ E) → ℝ := fun i => ‖C (v i)‖
  let W : E →ₗ[ℝ] F := ∑ i, (σ i)⁻¹ • (innerₛₗ ℝ (v i)).smulRight (C (v i))
  have hWx : ∀ x, W x = ∑ i, ((σ i)⁻¹ * ⟪v i, x⟫_ℝ) • C (v i) := by
    intro x
    simp [W, LinearMap.sum_apply, mul_smul]
  have hWv : ∀ j, W (v j) = (σ j)⁻¹ • C (v j) := by
    intro j
    rw [hWx]
    simp [v.inner_eq_ite]
  refine ⟨W, ?_, ?_⟩
  · intro x
    have key : ‖W x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hWx,
        ← v.sum_inner_mul_inner x x]
      simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      simp_rw [show ∀ i j, ⟪C (v i), C (v j)⟫_ℝ = if i = j then σ i ^ 2 else 0 from
        fun i j => aux_mfs_orth C i j]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [real_inner_comm x (v i)]
      rcases eq_or_ne (σ i) 0 with h | h
      · rw [h]; simp; exact mul_self_nonneg _
      · field_simp
        rfl
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp key
  · rw [aux_mfs_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hWv, real_inner_smul_left, real_inner_self_eq_norm_sq]
    change σ j = (σ j)⁻¹ * σ j ^ 2
    rcases eq_or_ne (σ j) 0 with h | h
    · rw [h]; simp
    · field_simp

lemma aux_mfs_convex (A B : E →ₗ[ℝ] F) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a • A + b • B).singularValues.sum (fun _ s => s) ≤
      a * A.singularValues.sum (fun _ s => s) + b * B.singularValues.sum (fun _ s => s) := by
  obtain ⟨W, hW, hEq⟩ := aux_mfs_exists (a • A + b • B)
  rw [hEq]
  set v := aux_mfs_vb (a • A + b • B)
  have h1 := aux_mfs_upper W A hW v
  have h2 := aux_mfs_upper W B hW v
  calc _ = a * ∑ i, ⟪W (v i), A (v i)⟫_ℝ + b * ∑ i, ⟪W (v i), B (v i)⟫_ℝ := by
        simp [inner_add_right, real_inner_smul_right, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by gcongr

end aux_mfs_section

lemma aux_mfs_nuc_convex {n₁ n₂ : ℕ} (X Y : Mat n₁ n₂) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    nuclearNorm (a • X + b • Y) ≤ a * nuclearNorm X + b * nuclearNorm Y := by
  unfold nuclearNorm
  rw [map_add, map_smul, map_smul]
  exact aux_mfs_convex _ _ a b ha hb

lemma aux_mfs_frob_sq {n₁ n₂ : ℕ} (Z : Mat n₁ n₂) :
    frobNorm Z ^ 2 = ∑ i, ∑ j, Z i j * Z i j := by
  unfold frobNorm frobInner
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

end CaiCandesShen.ProximalLimit

open CaiCandesShen.ProximalLimit
open Filter Topology

theorem solution {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (X X' : Mat n₁ n₂) (hX : IsMinFrobeniusSolution f X)
    (hX' : IsMinFrobeniusSolution f X') :
    X = X' := by
  obtain ⟨⟨hXf, hXn⟩, hXF⟩ := hX
  obtain ⟨⟨hX'f, hX'n⟩, hX'F⟩ := hX'
  set M : Mat n₁ n₂ := (1/2 : ℝ) • X + (1/2 : ℝ) • X' with hM
  have hMf : Feasible f M := by
    intro i
    have := (hconv i).2 (Set.mem_univ X) (Set.mem_univ X') (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    have h1 := hXf i
    have h2 := hX'f i
    calc f i M ≤ (1/2:ℝ) • f i X + (1/2:ℝ) • f i X' := this
      _ ≤ 0 := by simp only [smul_eq_mul]; linarith
  have hMn : IsNuclearNormSolution f M := by
    refine ⟨hMf, fun Y hY => ?_⟩
    have c := aux_mfs_nuc_convex X X' (1/2) (1/2) (by norm_num) (by norm_num)
    have e1 := hXn X' hX'f
    have e2 := hXn Y hY
    have e3 := hX'n X hXf
    change nuclearNorm ((1/2 : ℝ) • X + (1/2 : ℝ) • X') ≤ nuclearNorm Y
    linarith
  have hle := hXF M hMn
  have hle1 := hXF X' ⟨hX'f, hX'n⟩
  have hle2 := hX'F X ⟨hXf, hXn⟩
  rw [aux_mfs_frob_sq, aux_mfs_frob_sq] at hle hle1 hle2
  have hid : ∑ i, ∑ j, (X i j - X' i j) ^ 2 =
      2 * ∑ i, ∑ j, X i j * X i j + 2 * ∑ i, ∑ j, X' i j * X' i j
        - 4 * ∑ i, ∑ j, M i j * M i j := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hzero : ∑ i, ∑ j, (X i j - X' i j) ^ 2 = 0 := by
    apply le_antisymm
    · rw [hid]; linarith
    · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg (X i j - X' i j))).mp hzero i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
    sq_nonneg (X i j - X' i j))).mp h1 j (Finset.mem_univ _)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  linarith
