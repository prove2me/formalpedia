-- Prove2me | solution 1 for EffResSparsify.Sampling.lemma_3_i
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:10:53.52686+00:00
-- url     : https://prove2.me/submissions/7c41022d-d43f-4a72-a8d8-d8d5c6fcdd66

import Mathlib
import Definitions.Def_EffResSparsify_Sampling_Defs

set_option autoImplicit false
open Matrix

namespace DEHelp
open HarmonicGames.Decomposition

section abs
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem starProj_congr {U U' : Submodule ℝ V} [U.HasOrthogonalProjection]
    [U'.HasOrthogonalProjection] (h : U = U') (y : V) :
    U.starProjection y = U'.starProjection y := by
  subst h; rfl

theorem range_restrict (M : V →ₗ[ℝ] V) :
    LinearMap.range (M ∘ₗ (LinearMap.ker M)ᗮ.subtype) = LinearMap.range M := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ LinearMap.ker M ⊔ (LinearMap.ker M)ᗮ := by
      rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; trivial
    obtain ⟨k, hk, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨z, hz⟩, ?_⟩
    simp [LinearMap.mem_ker.mp hk]

theorem pinv_mem (M : V →ₗ[ℝ] V) (y : V) : pinv M y ∈ (LinearMap.ker M)ᗮ := by
  unfold pinv
  simp

theorem M_pinv (M : V →ₗ[ℝ] V) (y : V) :
    M (pinv M y) = (LinearMap.range M).starProjection y := by
  set R := LinearMap.range (M ∘ₗ (LinearMap.ker M)ᗮ.subtype) with hR
  let e := LinearEquiv.ofInjective _ (pinv_restrict_injective M)
  have h1 : M (pinv M y) = ((R.orthogonalProjectionOnto y : R) : V) := by
    have h2 := congrArg Subtype.val (e.apply_symm_apply (R.orthogonalProjectionOnto y))
    exact h2
  rw [h1, Submodule.coe_orthogonalProjectionOnto_apply]
  exact starProj_congr (range_restrict M) y

theorem ker_eq_orth (M : V →ₗ[ℝ] V) (hM : M.IsSymmetric) :
    LinearMap.ker M = (LinearMap.range M)ᗮ := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_orthogonal, LinearMap.mem_range,
    forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · intro h y
    rw [hM y x, h, inner_zero_right]
  · intro h
    have := h (M x)
    rw [hM (M x) x] at this
    exact inner_self_eq_zero.mp this

theorem pinv_mem_range (M : V →ₗ[ℝ] V) (hM : M.IsSymmetric) (y : V) :
    pinv M y ∈ LinearMap.range M := by
  have := pinv_mem M y
  rwa [ker_eq_orth M hM, Submodule.orthogonal_orthogonal] at this

theorem M_pinv_M (M : V →ₗ[ℝ] V) (x : V) : M (pinv M (M x)) = M x := by
  rw [M_pinv, Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self M x)]

theorem pinv_unique (M : V →ₗ[ℝ] V) {x x' : V} (hx : x ∈ (LinearMap.ker M)ᗮ)
    (hx' : x' ∈ (LinearMap.ker M)ᗮ) (h : M x = M x') : x = x' := by
  have : x - x' ∈ LinearMap.ker M ⊓ (LinearMap.ker M)ᗮ :=
    ⟨by simp [h], Submodule.sub_mem _ hx hx'⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
  exact sub_eq_zero.mp this

theorem pinv_M_pinv (M : V →ₗ[ℝ] V) (y : V) : pinv M (M (pinv M y)) = pinv M y := by
  apply pinv_unique M (pinv_mem _ _) (pinv_mem _ _)
  exact M_pinv_M M (pinv M y)

theorem pinv_symm (M : V →ₗ[ℝ] V) (hM : M.IsSymmetric) (x y : V) :
    inner ℝ (pinv M x) y = inner ℝ x (pinv M y) := by
  have h2 : inner ℝ (pinv M x) (y - (LinearMap.range M).starProjection y) = 0 := by
    apply Submodule.inner_right_of_mem_orthogonal (pinv_mem M x)
    rw [Submodule.orthogonal_orthogonal, ker_eq_orth M hM]
    exact Submodule.sub_starProjection_mem_orthogonal y
  have h3 := Submodule.starProjection_inner_eq_zero x (pinv M y) (pinv_mem_range M hM y)
  rw [inner_sub_left] at h3
  calc inner ℝ (pinv M x) y
      = inner ℝ (pinv M x) ((LinearMap.range M).starProjection y) +
        inner ℝ (pinv M x) (y - (LinearMap.range M).starProjection y) := by
          rw [← inner_add_right]; congr 1; abel
    _ = inner ℝ (pinv M x) (M (pinv M y)) := by rw [h2, add_zero, M_pinv]
    _ = inner ℝ (M (pinv M x)) (pinv M y) := (hM _ _).symm
    _ = inner ℝ ((LinearMap.range M).starProjection x) (pinv M y) := by rw [M_pinv]
    _ = inner ℝ x (pinv M y) := by linarith

end abs
end DEHelp

namespace DEHelp
open EffResSparsify.Sampling HarmonicGames.Decomposition

section mat
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def Am (G : WGraph V E) : Matrix E V ℝ := G.sqrtWeightMatrix * G.incidence

theorem sqrtW_T (G : WGraph V E) : G.sqrtWeightMatrixᵀ = G.sqrtWeightMatrix := by
  simp [WGraph.sqrtWeightMatrix]

theorem lap_eq (G : WGraph V E) : G.laplacian = (Am G)ᵀ * Am G := by
  have h : G.sqrtWeightMatrix * G.sqrtWeightMatrix = G.weightMatrix := by
    simp only [WGraph.sqrtWeightMatrix, WGraph.weightMatrix, Matrix.diagonal_mul_diagonal]
    congr 1; funext e; exact Real.mul_self_sqrt (G.w_pos e).le
  simp only [WGraph.laplacian, Am, Matrix.transpose_mul, sqrtW_T, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc G.sqrtWeightMatrix, h]

theorem lap_T (G : WGraph V E) : G.laplacianᵀ = G.laplacian := by
  conv_rhs => rw [lap_eq]
  conv_lhs => rw [lap_eq]
  simp [Matrix.transpose_mul]

noncomputable def LM (G : WGraph V E) : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
  Matrix.toEuclideanLin G.laplacian

theorem LM_symm (G : WGraph V E) : (LM G).IsSymmetric := by
  unfold LM
  rw [Matrix.isSymmetric_toEuclideanLin_iff]
  simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, lap_T]

theorem tEL_mul (A B : Matrix V V ℝ) (v : EuclideanSpace ℝ V) :
    Matrix.toEuclideanLin (A * B) v =
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]

theorem tEL_P (G : WGraph V E) :
    Matrix.toEuclideanLin G.lapPinv = pinv (LM G) := by
  unfold WGraph.lapPinv LM
  simp

theorem P_symm (G : WGraph V E) : G.lapPinvᵀ = G.lapPinv := by
  have h : (Matrix.toEuclideanLin G.lapPinv).IsSymmetric := by
    rw [tEL_P]; exact fun x y => pinv_symm (LM G) (LM_symm G) x y
  have := (Matrix.isSymmetric_toEuclideanLin_iff.mp h).eq
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

theorem P_L_P (G : WGraph V E) : G.lapPinv * G.laplacian * G.lapPinv = G.lapPinv := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro v
  rw [tEL_mul, tEL_mul, tEL_P]
  have : Matrix.toEuclideanLin G.laplacian = LM G := rfl
  rw [this]
  exact pinv_M_pinv (LM G) v

theorem L_P_L (G : WGraph V E) : G.laplacian * G.lapPinv * G.laplacian = G.laplacian := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro v
  rw [tEL_mul, tEL_mul, tEL_P]
  have : Matrix.toEuclideanLin G.laplacian = LM G := rfl
  rw [this]
  exact M_pinv_M (LM G) v

theorem A_P_L (G : WGraph V E) : Am G * G.lapPinv * G.laplacian = Am G := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  have hk : G.laplacian *ᵥ (x - G.lapPinv *ᵥ (G.laplacian *ᵥ x)) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, L_P_L, sub_self]
  have hA : Am G *ᵥ (x - G.lapPinv *ᵥ (G.laplacian *ᵥ x)) = 0 := by
    set k := x - G.lapPinv *ᵥ (G.laplacian *ᵥ x)
    have h1 : (Am G *ᵥ k) ⬝ᵥ (Am G *ᵥ k) = 0 := by
      have : k ⬝ᵥ ((Am G)ᵀ *ᵥ (Am G *ᵥ k)) = 0 := by
        rw [Matrix.mulVec_mulVec, ← lap_eq, hk, dotProduct_zero]
      rwa [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at this
    exact dotProduct_self_eq_zero.mp h1
  rw [Matrix.mulVec_sub] at hA
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  exact (sub_eq_zero.mp hA).symm

theorem Pi_eq (G : WGraph V E) : G.projPi = Am G * G.lapPinv * (Am G)ᵀ := by
  simp [WGraph.projPi, Am, Matrix.transpose_mul, sqrtW_T, Matrix.mul_assoc]

theorem Pi_idem (G : WGraph V E) : G.projPi * G.projPi = G.projPi := by
  have : G.projPi * G.projPi =
      Am G * (G.lapPinv * ((Am G)ᵀ * Am G) * G.lapPinv) * (Am G)ᵀ := by
    rw [Pi_eq]; simp only [Matrix.mul_assoc]
  rw [this, ← lap_eq, P_L_P, Pi_eq]

theorem Pi_symm (G : WGraph V E) : G.projPiᵀ = G.projPi := by
  rw [Pi_eq]
  simp [Matrix.transpose_mul, P_symm, Matrix.mul_assoc]

end mat
end DEHelp
open DEHelp in

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EffResSparsify.Sampling.WGraph V E) (hG : G.IsConnected) :
    G.projPi * G.projPi = G.projPi ∧ G.projPiᵀ = G.projPi :=
  ⟨Pi_idem G, Pi_symm G⟩
