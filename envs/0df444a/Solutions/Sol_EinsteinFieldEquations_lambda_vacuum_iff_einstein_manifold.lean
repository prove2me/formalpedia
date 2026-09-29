-- Prove2me | solution 1 for EinsteinFieldEquations.lambda_vacuum_iff_einstein_manifold
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-24T06:36:31.919433+00:00
-- url     : https://prove2.me/submissions/a055ce30-f6f1-4bfe-a959-e65aa5e0fb2e

import Mathlib
import Definitions.Def_efe_geometry

open EinsteinFieldEquations

noncomputable section

def W7a_EFE_A : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, -1, -1; 1, -1, 0, 0; -1, -1, 0, 0; 0, 1, -1, 0]

def W7a_EFE_B : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1/2, -1/2, 0; 0, -1/2, -1/2, 0; 0, -1/2, -1/2, -1; -1, 0, 0, 1]

def W7a_EFE_u : Fin 4 → ℝ := ![-1, 0, -1, 1]

def W7a_EFE_Au : Fin 4 → ℝ := ![0, -1, 1, 1]

def W7a_EFE_W : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![![![0, -2, 2, 2], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 1, 0, 0], ![4, 3, -4, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 2, -2, 0]]]

def W7a_EFE_phi (y : Coord) (j : Fin 4) : ℝ :=
  (1 / 2) * ∑ k : Fin 4, ∑ l : Fin 4, W7a_EFE_W k l j * y k * y l

/-- the partial derivative `∂_k φ_j` as a linear map of `y` -/
def W7a_EFE_L (k j : Fin 4) : Coord →L[ℝ] ℝ :=
  ∑ l : Fin 4, W7a_EFE_W k l j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) l

def W7a_EFE_g : Tensor2Field := fun y =>
  Matrix.of fun i j => W7a_EFE_A i j + W7a_EFE_Au i * W7a_EFE_phi y j

def W7a_EFE_ginv (y : Coord) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a d => W7a_EFE_B a d - W7a_EFE_u a * ∑ m : Fin 4, W7a_EFE_phi y m * W7a_EFE_B m d

theorem W7a_EFE_L_apply (k j : Fin 4) (y : Coord) :
    W7a_EFE_L k j y = ∑ l : Fin 4, W7a_EFE_W k l j * y l := by
  simp [W7a_EFE_L]

theorem W7a_EFE_phi_explicit (y : Coord) :
    W7a_EFE_phi y = ![2 * y 1 ^ 2 + y 3 ^ 2,
      -y 0 ^ 2 + 3 / 2 * y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 + y 0 * y 1,
      y 0 ^ 2 - 2 * y 1 ^ 2 - y 3 ^ 2, y 0 ^ 2] := by
  funext j
  fin_cases j <;> simp [W7a_EFE_phi, W7a_EFE_W, Fin.sum_univ_four] <;> ring

theorem W7a_EFE_phi_hasFDerivAt (j : Fin 4) (y : Coord) :
    HasFDerivAt (fun y => W7a_EFE_phi y j)
      (∑ m : Fin 4, W7a_EFE_L m j y • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 4 => ℝ) m) y := by
  have hc : ∀ k : Fin 4, HasFDerivAt (fun y : Coord => y k)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) k) y :=
    fun k => hasFDerivAt_apply k y
  have h1 (k l : Fin 4) := ((hc k).const_mul (W7a_EFE_W k l j)).mul (hc l)
  have h := (HasFDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) fun l _ => h1 k l).const_mul (1 / 2 : ℝ)
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_sum', Pi.smul_apply,
    Finset.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    smul_eq_mul, W7a_EFE_L_apply, ContinuousLinearMap.proj_apply]
  fin_cases j <;> simp [W7a_EFE_W, Fin.sum_univ_four] <;> ring

theorem W7a_EFE_pd_g (i j k : Fin 4) (y : Coord) :
    partialD (fun y => W7a_EFE_g y i j) k y = W7a_EFE_Au i * W7a_EFE_L k j y := by
  have e : (fun y => W7a_EFE_g y i j) =
      fun y => W7a_EFE_A i j + W7a_EFE_Au i * W7a_EFE_phi y j := by
    funext y; simp [W7a_EFE_g]
  unfold partialD
  rw [e, (((W7a_EFE_phi_hasFDerivAt j y).const_mul (W7a_EFE_Au i)).const_add
    (W7a_EFE_A i j)).fderiv]
  simp [Pi.single_apply]

theorem W7a_EFE_BA : W7a_EFE_B * W7a_EFE_A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W7a_EFE_A, W7a_EFE_B, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

theorem W7a_EFE_ginv_eq (y : Coord) : (W7a_EFE_g y)⁻¹ = W7a_EFE_ginv y := by
  apply Matrix.inv_eq_left_inv
  ext i j
  simp only [W7a_EFE_g, W7a_EFE_ginv, W7a_EFE_phi_explicit, Matrix.mul_apply, Matrix.of_apply,
    Fin.sum_univ_four, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [W7a_EFE_A, W7a_EFE_B, W7a_EFE_u, W7a_EFE_Au] <;> ring

theorem W7a_EFE_g0 : W7a_EFE_g 0 = W7a_EFE_A := by
  ext i j
  simp [W7a_EFE_g, W7a_EFE_phi]

theorem W7a_EFE_ginv0 : W7a_EFE_ginv 0 = W7a_EFE_B := by
  ext i j
  simp [W7a_EFE_ginv, W7a_EFE_phi]

theorem W7a_EFE_pd_sum_mul (P : Fin 4 → Coord → ℝ) (Q : Fin 4 → (Coord →L[ℝ] ℝ))
    (hP : ∀ d, DifferentiableAt ℝ (P d) 0) (e : Fin 4) :
    partialD (fun y => ∑ d : Fin 4, P d y * Q d y) e 0 =
      ∑ d : Fin 4, P d 0 * Q d (Pi.single e 1) := by
  have h : HasFDerivAt (fun y => ∑ d : Fin 4, P d y * Q d y)
      (∑ d : Fin 4, (P d 0 • Q d + Q d 0 • fderiv ℝ (P d) 0)) 0 :=
    HasFDerivAt.fun_sum fun d _ => (hP d).hasFDerivAt.mul (Q d).hasFDerivAt
  unfold partialD
  rw [h.fderiv]
  simp

def W7a_EFE_Q (a b c d : Fin 4) : Coord →L[ℝ] ℝ :=
  W7a_EFE_Au d • W7a_EFE_L b c + W7a_EFE_Au d • W7a_EFE_L c b - W7a_EFE_Au b • W7a_EFE_L d c

theorem W7a_EFE_chr (a b c : Fin 4) :
    (fun y => christoffel W7a_EFE_g a b c y) =
      fun y => ∑ d : Fin 4, (1 / 2 * W7a_EFE_ginv y a d) * W7a_EFE_Q a b c d y := by
  funext y
  simp only [christoffel, W7a_EFE_ginv_eq, W7a_EFE_pd_g, Finset.mul_sum, W7a_EFE_Q]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem W7a_EFE_diffP (a d : Fin 4) :
    DifferentiableAt ℝ (fun y => 1 / 2 * W7a_EFE_ginv y a d) 0 := by
  have hphi : ∀ m, DifferentiableAt ℝ (fun y => W7a_EFE_phi y m) 0 :=
    fun m => (W7a_EFE_phi_hasFDerivAt m 0).differentiableAt
  simp only [W7a_EFE_ginv, Matrix.of_apply]
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.sub (differentiableAt_const _)
  apply DifferentiableAt.const_mul
  exact DifferentiableAt.fun_sum fun m _ => (hphi m).mul (differentiableAt_const _)

theorem W7a_EFE_pd_chr (a b c e : Fin 4) :
    partialD (fun y => christoffel W7a_EFE_g a b c y) e 0 =
      ∑ d : Fin 4, (1 / 2 * W7a_EFE_B a d) * W7a_EFE_Q a b c d (Pi.single e 1) := by
  rw [W7a_EFE_chr, W7a_EFE_pd_sum_mul (fun d y => 1 / 2 * W7a_EFE_ginv y a d)
    (fun d => W7a_EFE_Q a b c d) (fun d => W7a_EFE_diffP a d) e]
  simp [W7a_EFE_ginv0]

theorem W7a_EFE_chr0 (a b c : Fin 4) : christoffel W7a_EFE_g a b c 0 = 0 := by
  rw [show christoffel W7a_EFE_g a b c 0 = (fun y => christoffel W7a_EFE_g a b c y) 0 from rfl,
    W7a_EFE_chr]
  simp

theorem W7a_EFE_ricci (b d : Fin 4) : ricci W7a_EFE_g b d 0 = W7a_EFE_A b d := by
  simp only [ricci, riemann, W7a_EFE_pd_chr, W7a_EFE_chr0, mul_zero, sub_zero,
    Finset.sum_const_zero, add_zero]
  simp only [W7a_EFE_Q, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, W7a_EFE_L_apply, Fin.sum_univ_four]
  fin_cases b <;> fin_cases d <;>
    simp [W7a_EFE_A, W7a_EFE_B, W7a_EFE_Au, W7a_EFE_W, Pi.single_apply] <;> norm_num

theorem W7a_EFE_Ainv : W7a_EFE_A⁻¹ = W7a_EFE_B := Matrix.inv_eq_left_inv W7a_EFE_BA

theorem W7a_EFE_scalar : scalarCurvature W7a_EFE_g 0 = 2 := by
  simp only [scalarCurvature, metricTrace, Matrix.of_apply, W7a_EFE_ricci, W7a_EFE_g0,
    W7a_EFE_Ainv, Fin.sum_univ_four]
  simp [W7a_EFE_A, W7a_EFE_B]
  norm_num

end

theorem solution : ¬ (∀ (g : Tensor2Field) (Lam kappa : ℝ) (x : Coord),
    IsUnit (g x).det →
    (SatisfiesEFE g Lam kappa (fun _ => 0) x ↔
      ∀ a b : Fin 4, ricci g a b x = Lam * (g x) a b)) := by
  intro h
  have hdet : IsUnit (W7a_EFE_g 0).det := by
    rw [W7a_EFE_g0]; exact Matrix.isUnit_det_of_left_inverse W7a_EFE_BA
  have hR : ∀ a b : Fin 4, ricci W7a_EFE_g a b 0 = 1 * (W7a_EFE_g 0) a b := by
    intro a b
    rw [W7a_EFE_ricci, W7a_EFE_g0, one_mul]
  have h01 := (h W7a_EFE_g 1 1 0 hdet).mpr hR 0 1
  simp only [einsteinTensor, W7a_EFE_ricci, W7a_EFE_scalar, W7a_EFE_g0] at h01
  simp [W7a_EFE_A] at h01
