-- Prove2me | solution 1 for BoydADMM.L1.basis_pursuit_x_update
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T08:01:48.545418+00:00
-- url     : https://prove2.me/submissions/a87b6d2a-d069-4160-b085-010e8849f41a

import Definitions.Def_BoydADMM_L1_Basic
set_option autoImplicit false
section
set_option autoImplicit false
open Matrix
namespace ADMMCodex
open BoydADMM.L1
 theorem projection_closed_form {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (hA : (A*Aᵀ).det≠0) (v : EuclideanSpace ℝ (Fin n)) :
    IsUniqueMinimizerOn (fun x : EuclideanSpace ℝ (Fin n) => ‖x-v‖)
      {x | Matrix.toEuclideanLin A x=b}
      (Matrix.toEuclideanLin (1-Aᵀ*(A*Aᵀ)⁻¹*A) v+
        Matrix.toEuclideanLin (Aᵀ*(A*Aᵀ)⁻¹) b) := by
  let F := Matrix.toEuclideanLin A
  let G := Matrix.toEuclideanLin Aᵀ
  let B := Matrix.toEuclideanLin (A*Aᵀ)⁻¹
  let c := Matrix.toEuclideanLin (1-Aᵀ*(A*Aᵀ)⁻¹*A) v+
    Matrix.toEuclideanLin (Aᵀ*(A*Aᵀ)⁻¹) b
  have hid : F ∘ₗ G ∘ₗ B = LinearMap.id := by
    change (Matrix.toLpLin 2 2 A) ∘ₗ (Matrix.toLpLin 2 2 Aᵀ) ∘ₗ
      (Matrix.toLpLin 2 2 (A*Aᵀ)⁻¹) = _
    rw [← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), Matrix.toLpLin_one]
  have he (w : EuclideanSpace ℝ (Fin m)) : F (G (B w))=w := by
    have := congrArg (fun L : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) => L w) hid
    exact this
  have hc : c=v-G (B (F v-b)) := by
    simp only [c,F,G,B,Matrix.toEuclideanLin,map_sub,Matrix.toLpLin_mul_same,
      LinearMap.sub_apply, Matrix.toLpLin_one, LinearMap.id_apply, LinearMap.comp_apply]
    abel
  have hfeas : F c=b := by rw [hc,map_sub,he];abel
  have hG : G=F.adjoint := by
    simpa only [F,G,conjTranspose_eq_transpose_of_trivial] using A.toEuclideanLin_conjTranspose_eq_adjoint
  have gap (y : EuclideanSpace ℝ (Fin n)) (hy : F y=b) : ‖y-v‖^2=‖c-v‖^2+‖y-c‖^2 := by
    have hker : F (y-c)=0 := by rw [map_sub,hy,hfeas,sub_self]
    have hr : c-v= -G (B (F v-b)) := by rw [hc];abel
    have hi : inner ℝ (c-v) (y-c)=0 := by
      rw [hr,inner_neg_left,hG,LinearMap.adjoint_inner_left,hker,inner_zero_right,neg_zero]
    have hd : y-v=(c-v)+(y-c) := by abel
    rw [hd,norm_add_sq_real,hi]
    ring
  refine ⟨hfeas, ?_, ?_⟩
  · intro y hy
    have hg := gap y hy
    nlinarith [norm_nonneg (c-v), norm_nonneg (y-v), sq_nonneg ‖y-c‖]
  · intro y hy hm
    change ‖y-v‖ ≤ ‖c-v‖ at hm
    have hg := gap y hy
    have hz : ‖y-c‖=0 := by
      nlinarith [norm_nonneg (c-v), norm_nonneg (y-v), norm_nonneg (y-c)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
end ADMMCodex

end

set_option autoImplicit false
open Matrix BoydADMM.L1
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (hA : (A * Aᵀ).det ≠ 0) (z u : EuclideanSpace ℝ (Fin n)) :
    IsUniqueMinimizerOn (fun x : EuclideanSpace ℝ (Fin n) => ‖x - (z - u)‖)
      {x | Matrix.toEuclideanLin A x = b}
      (Matrix.toEuclideanLin (1 - Aᵀ * (A * Aᵀ)⁻¹ * A) (z - u) +
        Matrix.toEuclideanLin (Aᵀ * (A * Aᵀ)⁻¹) b) := by
  exact ADMMCodex.projection_closed_form A b hA (z-u)



#print axioms solution
