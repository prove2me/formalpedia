-- Prove2me | solution 1 for BoydADMM.L1.lasso_updates
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T08:01:47.223442+00:00
-- url     : https://prove2.me/submissions/6b902b61-642d-4ae1-b3dd-04b964b36ebd

import Definitions.Def_BoydADMM_L1_Basic
import Definitions.Def_HighDimStat_SparseLinear_L1Norm
set_option autoImplicit false
section
set_option autoImplicit false
open Matrix
namespace ADMMCodex
open BoydADMM.L1
 theorem ridge_gap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (v c y : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
    (hstat : (Matrix.toEuclideanLin A).adjoint (Matrix.toEuclideanLin A c-b)+ρ • (c-v)=0) :
    ((1/2)*‖Matrix.toEuclideanLin A y-b‖^2+(ρ/2)*‖y-v‖^2) -
      ((1/2)*‖Matrix.toEuclideanLin A c-b‖^2+(ρ/2)*‖c-v‖^2) =
        (1/2)*‖Matrix.toEuclideanLin A (y-c)‖^2+(ρ/2)*‖y-c‖^2 := by
  have ha : Matrix.toEuclideanLin A y-b = (Matrix.toEuclideanLin A c-b)+
      Matrix.toEuclideanLin A (y-c) := by rw [map_sub];abel
  have hv : y-v=(c-v)+(y-c) := by abel
  have hs := congrArg (fun w => inner ℝ w (y-c)) hstat
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left,
    LinearMap.adjoint_inner_left] at hs
  rw [ha, hv, norm_add_sq_real, norm_add_sq_real]
  nlinarith
 theorem ridge_unique_of_stationary {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (v c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : 0<ρ)
    (hstat : (Matrix.toEuclideanLin A).adjoint (Matrix.toEuclideanLin A c-b)+ρ • (c-v)=0) :
    IsUniqueMinimizerOn (fun y : EuclideanSpace ℝ (Fin n) =>
      (1/2)*‖Matrix.toEuclideanLin A y-b‖^2+(ρ/2)*‖y-v‖^2) Set.univ c := by
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · intro y _
    have hg := ridge_gap A b v c y ρ hstat
    have hn := sq_nonneg ‖Matrix.toEuclideanLin A (y-c)‖
    have ht := mul_nonneg (le_of_lt (half_pos hρ)) (sq_nonneg ‖y-c‖)
    linarith
  · intro y _ hm
    change (1/2)*‖Matrix.toEuclideanLin A y-b‖^2+(ρ/2)*‖y-v‖^2 ≤
      (1/2)*‖Matrix.toEuclideanLin A c-b‖^2+(ρ/2)*‖c-v‖^2 at hm
    have hg := ridge_gap A b v c y ρ hstat
    have hn := sq_nonneg ‖Matrix.toEuclideanLin A (y-c)‖
    have hle : (ρ/2)*‖y-c‖^2 ≤ 0 := by linarith
    have hs : ‖y-c‖^2 ≤ 0 := by
      by_contra h
      have hp := mul_pos (half_pos hρ) (lt_of_not_ge h)
      linarith
    have hz : ‖y-c‖=0 := by nlinarith [norm_nonneg (y-c)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
 theorem ridge_closed_form {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : 0<ρ) :
    IsUniqueMinimizerOn (fun y : EuclideanSpace ℝ (Fin n) =>
      (1/2)*‖Matrix.toEuclideanLin A y-b‖^2+(ρ/2)*‖y-v‖^2) Set.univ
      (Matrix.toEuclideanLin (Aᵀ*A+ρ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹
        (Matrix.toEuclideanLin Aᵀ b+ρ • v)) := by
  let M := Aᵀ*A+ρ • (1 : Matrix (Fin n) (Fin n) ℝ)
  have hM : M.PosDef := by
    have ha : (Aᵀ*A).PosSemidef := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self A
    exact Matrix.PosDef.posSemidef_add ha (Matrix.PosDef.one.smul hρ)
  let c := Matrix.toEuclideanLin M⁻¹ (Matrix.toEuclideanLin Aᵀ b+ρ • v)
  have he : Matrix.toEuclideanLin M c = Matrix.toEuclideanLin Aᵀ b+ρ • v := by
    change (Matrix.toLpLin 2 2 M) ((Matrix.toLpLin 2 2 M⁻¹) _) = _
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, M.mul_nonsing_inv ((isUnit_iff_isUnit_det M).mp hM.isUnit), Matrix.toLpLin_one]
    rfl
  apply ridge_unique_of_stationary A b v c ρ hρ
  have ht : Matrix.toEuclideanLin Aᵀ = (Matrix.toEuclideanLin A).adjoint := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using A.toEuclideanLin_conjTranspose_eq_adjoint
  have he' : (Matrix.toEuclideanLin A).adjoint (Matrix.toEuclideanLin A c)+ρ • c =
      (Matrix.toEuclideanLin A).adjoint b+ρ • v := by
    simpa only [M, map_add, map_smul, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Matrix.toLpLin_one,
      LinearMap.id_apply, ← ht] using he
  calc
    _ = ((Matrix.toEuclideanLin A).adjoint (Matrix.toEuclideanLin A c)+ρ • c) -
        ((Matrix.toEuclideanLin A).adjoint b+ρ • v) := by rw [map_sub, smul_sub];abel
    _ = 0 := sub_eq_zero.mpr he'

end ADMMCodex

end

section
set_option autoImplicit false
namespace ADMMCodex
open BoydADMM.Prox
 theorem soft_subgradient (lam ρ a z : ℝ) (hlam : 0≤lam) (hρ : 0<ρ) :
    lam * |softThreshold (lam/ρ) a| +
      ρ * (a-softThreshold (lam/ρ) a) * (z-softThreshold (lam/ρ) a) ≤ lam * |z| := by
  have hk : 0≤lam/ρ := div_nonneg hlam (le_of_lt hρ)
  have hmul : ρ * (lam/ρ)=lam := by field_simp
  by_cases hp : lam/ρ < a
  · simp only [softThreshold, if_pos hp]
    have ht : 0<a-lam/ρ := sub_pos.mpr hp
    have he : ρ*(a-(a-lam/ρ))=lam := by nlinarith [hmul]
    rw [abs_of_pos ht, he]
    nlinarith [mul_le_mul_of_nonneg_left (le_abs_self z) hlam]
  · by_cases hn : a < -(lam/ρ)
    · simp only [softThreshold, if_neg hp, if_pos hn]
      have ht : a+lam/ρ < 0 := by linarith
      have he : ρ*(a-(a+lam/ρ))= -lam := by nlinarith [hmul]
      rw [abs_of_neg ht, he]
      nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs z) hlam]
    · simp only [softThreshold, if_neg hp, if_neg hn, abs_zero, mul_zero, sub_zero, zero_add]
      have hu : ρ*a ≤ lam := by
        have := mul_le_mul_of_nonneg_left (le_of_not_gt hp) (le_of_lt hρ)
        nlinarith [hmul]
      have hl : -lam ≤ ρ*a := by
        have := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (le_of_lt hρ)
        nlinarith [hmul]
      by_cases hz : 0≤z
      · rw [abs_of_nonneg hz]
        exact mul_le_mul_of_nonneg_right hu hz
      · rw [abs_of_neg (lt_of_not_ge hz)]
        nlinarith [mul_le_mul_of_nonpos_right hl (le_of_lt (lt_of_not_ge hz))]
 theorem soft_gap (lam ρ a z : ℝ) (hlam : 0≤lam) (hρ : 0<ρ) :
    (ρ/2)*(z-softThreshold (lam/ρ) a)^2 ≤
      (lam*|z|+(ρ/2)*(a-z)^2) -
        (lam*|softThreshold (lam/ρ) a|+(ρ/2)*(a-softThreshold (lam/ρ) a)^2) := by
  have h := soft_subgradient lam ρ a z hlam hρ
  nlinarith
end ADMMCodex

end

section
set_option autoImplicit false
namespace ADMMCodex
open BoydADMM.L1 BoydADMM.Prox
 theorem vector_l1_objective_sum {n : ℕ} (lam ρ : ℝ) (v z : EuclideanSpace ℝ (Fin n)) :
    lam*HighDimStat.SparseLinear.l1Norm (WithLp.ofLp z)+(ρ/2)*‖v-z‖^2 =
      ∑ i, (lam*|z i|+(ρ/2)*(v i-z i)^2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold HighDimStat.SparseLinear.l1Norm
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  rfl
 theorem vector_threshold {n : ℕ} (lam ρ : ℝ) (hlam : 0≤lam) (hρ : 0<ρ)
    (x u : EuclideanSpace ℝ (Fin n)) :
    IsUniqueMinimizerOn
      (fun z : EuclideanSpace ℝ (Fin n) => lam*HighDimStat.SparseLinear.l1Norm (WithLp.ofLp z)+
        (ρ/2)*‖x-z+u‖^2) Set.univ
      (WithLp.toLp 2 fun i => softThreshold (lam/ρ) (x i+u i)) := by
  let T : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => softThreshold (lam/ρ) (x i+u i)
  have hn (z : EuclideanSpace ℝ (Fin n)) : x-z+u=(x+u)-z := by abel
  have gap (z : EuclideanSpace ℝ (Fin n)) : (ρ/2)*‖z-T‖^2 ≤
      (lam*HighDimStat.SparseLinear.l1Norm (WithLp.ofLp z)+(ρ/2)*‖x-z+u‖^2) -
        (lam*HighDimStat.SparseLinear.l1Norm (WithLp.ofLp T)+(ρ/2)*‖x-T+u‖^2) := by
    rw [hn z, hn T, vector_l1_objective_sum, vector_l1_objective_sum,
      EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    exact soft_gap lam ρ (x i+u i) (z i) hlam hρ
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · intro z _
    have hg := gap z
    have hp := mul_nonneg (le_of_lt (half_pos hρ)) (sq_nonneg ‖z-T‖)
    linarith
  · intro z _ hm
    change lam*HighDimStat.SparseLinear.l1Norm (WithLp.ofLp z)+(ρ/2)*‖x-z+u‖^2 ≤
      lam*HighDimStat.SparseLinear.l1Norm (WithLp.ofLp T)+(ρ/2)*‖x-T+u‖^2 at hm
    have hg := gap z
    have hle : (ρ/2)*‖z-T‖^2 ≤ 0 := le_trans hg (sub_nonpos.mpr hm)
    have hs : ‖z-T‖^2 ≤ 0 := by
      by_contra h
      have hp := mul_pos (half_pos hρ) (lt_of_not_ge h)
      linarith
    have hp := norm_nonneg (z-T)
    have hz : ‖z-T‖=0 := by nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
end ADMMCodex

end

set_option autoImplicit false
open Matrix BoydADMM.L1
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (lam ρ : ℝ) (hlam : 0 ≤ lam) (hρ : 0 < ρ) (z u : EuclideanSpace ℝ (Fin n)) :
    IsUniqueMinimizerOn
        (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 / 2) * ‖Matrix.toEuclideanLin A x - b‖ ^ 2 + (ρ / 2) * ‖x - z + u‖ ^ 2) Set.univ
        (Matrix.toEuclideanLin (Aᵀ * A + ρ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹
          (Matrix.toEuclideanLin Aᵀ b + ρ • (z - u))) ∧
      ∀ x : EuclideanSpace ℝ (Fin n),
        IsUniqueMinimizerOn
          (fun z' : EuclideanSpace ℝ (Fin n) =>
            lam * HighDimStat.SparseLinear.l1Norm (WithLp.ofLp z') +
              (ρ / 2) * ‖x - z' + u‖ ^ 2) Set.univ
          (WithLp.toLp 2 fun i => BoydADMM.Prox.softThreshold (lam / ρ) (x i + u i)) := by
  constructor
  · have he (y : EuclideanSpace ℝ (Fin n)) : y-(z-u)=y-z+u := by abel
    simpa only [he] using ADMMCodex.ridge_closed_form A b (z-u) ρ hρ
  · intro x
    exact ADMMCodex.vector_threshold lam ρ hlam hρ x u



#print axioms solution
