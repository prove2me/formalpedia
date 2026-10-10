-- Prove2me | solution 1 for ConleyZehnder.signature_eq_zero_of_hyperbolic
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T23:30:05.780446+00:00
-- url     : https://prove2.me/submissions/b7e6ff83-969e-4e6e-aeda-bb078c8a0ca8

import Definitions.Def_ConleyZehnder_Setting
import Theorems.Thm_ConleyZehnder_argLift_exists_increment_unique
import Theorems.Thm_ConleyZehnder_complexLinearDet_mul_four_pow
import Theorems.Thm_ConleyZehnder_argLift_square_increment
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.Complex.Polynomial.Basic

open ConleyZehnder Matrix
open ConleyZehnder Matrix Module Polynomial
open ConleyZehnder Matrix Module

namespace CZ13

variable {n : ℕ}

/-- complexified matrix -/
noncomputable abbrev cx (M : Mat n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  M.map (fun x : ℝ => (x : ℂ))

lemma cx_eq (M : Mat n) : cx M = (Complex.ofRealHom).mapMatrix M := rfl

lemma cx_mul (M N : Mat n) : cx (M * N) = cx M * cx N := by
  simp only [cx_eq, map_mul]

lemma cx_one : cx (1 : Mat n) = 1 := by simp only [cx_eq, map_one]

lemma cx_det (M : Mat n) : (cx M).det = (M.det : ℂ) := by
  rw [cx_eq, ← RingHom.map_det]; rfl

/-- `det (a • 1 + b • M)` for the complexification of `M`. -/
noncomputable def Q (a b : ℂ) (M : Mat n) : ℂ := (a • (1 : Matrix _ _ ℂ) + b • cx M).det

noncomputable def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

lemma norm_phase {z : ℂ} (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  rw [phase, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.2 hz)]

lemma phase_eq_exp {z : ℂ} (hz : z ≠ 0) : phase z = Complex.exp (z.arg * Complex.I) := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  rw [phase, div_eq_iff hn]
  exact h.symm.trans (mul_comm _ _)

lemma phase_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    phase (∏ i ∈ s, f i) = ∏ i ∈ s, phase (f i) := by
  simp only [phase, norm_prod, Complex.ofReal_prod, Finset.prod_div_distrib]

lemma phase_real_mul_sq {c : ℝ} (hc : c ≠ 0) (w : ℂ) : phase ((c : ℂ) * w) ^ 2 = phase w ^ 2 := by
  have hcc : ((|c| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.2 hc
  have h2 : ((c : ℂ) / ((|c| : ℝ) : ℂ)) ^ 2 = 1 := by
    rw [div_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs, div_self]
    exact_mod_cast pow_ne_zero 2 hc
  simp only [phase, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul]
  rw [show (c : ℂ) * w / (((|c| : ℝ) : ℂ) * ((‖w‖ : ℝ) : ℂ)) =
      ((c : ℂ) / ((|c| : ℝ) : ℂ)) * (w / ((‖w‖ : ℝ) : ℂ)) by
    rw [mul_div_mul_comm], mul_pow, h2, one_mul]

lemma phase_real_sq {c : ℝ} (hc : c ≠ 0) : phase (c : ℂ) ^ 2 = 1 := by
  have := phase_real_mul_sq hc 1
  rw [mul_one] at this
  rw [this]; simp [phase]

/-! ### Spectral decomposition of a real symmetric matrix -/

/-- the orthogonal eigenvector matrix -/
noncomputable def evU {N : Mat n} (hN : N.IsHermitian) : Mat n := (hN.eigenvectorUnitary : Mat n)

lemma evU_spec {N : Mat n} (hN : N.IsHermitian) :
    N = evU hN * diagonal hN.eigenvalues * (evU hN)ᵀ ∧ (evU hN)ᵀ * evU hN = 1 ∧
      evU hN * (evU hN)ᵀ = 1 := by
  have h1 := hN.spectral_theorem
  have hs : (star (hN.eigenvectorUnitary : Mat n)) = (evU hN)ᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]; rfl
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [h1]
    rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp, hs]
    rfl
  · rw [← hs]; exact Unitary.coe_star_mul_self _
  · rw [← hs]; exact Unitary.coe_mul_star_self _

lemma Q_conj {U : Mat n} (hU : U * Uᵀ = 1) (d : Fin n ⊕ Fin n → ℝ) (a b : ℂ) :
    Q a b (U * diagonal d * Uᵀ) = ∏ i, (a + b * d i) := by
  have hdiag : diagonal (fun i => a + b * d i) = a • (1 : Matrix _ _ ℂ) + b • cx (diagonal d) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [diagonal]
    · simp [diagonal, h, one_apply]
  have hUU : cx U * cx Uᵀ = 1 := by rw [← cx_mul, hU, cx_one]
  have key : a • (1 : Matrix _ _ ℂ) + b • cx (U * diagonal d * Uᵀ) =
      cx U * diagonal (fun i => a + b * d i) * cx Uᵀ := by
    rw [hdiag, cx_mul, cx_mul, Matrix.mul_add, Matrix.add_mul, mul_smul_comm, smul_mul_assoc,
      Matrix.mul_one, hUU, mul_smul_comm, smul_mul_assoc]
  unfold Q
  rw [key, det_mul, det_mul, det_diagonal]
  have : (cx U).det * (cx Uᵀ).det = 1 := by rw [← det_mul, hUU, det_one]
  linear_combination (∏ i, (a + b * d i)) * this

lemma Q_symm {N : Mat n} (hN : N.IsHermitian) (a b : ℂ) :
    Q a b N = ∏ i, (a + b * hN.eigenvalues i) := by
  obtain ⟨h1, -, h3⟩ := evU_spec hN
  conv_lhs => rw [h1]
  exact Q_conj h3 _ a b

lemma isHermitian_of_transpose {M : Mat n} (h : Mᵀ = M) : M.IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, h]

lemma Q_ne_zero_one {N : Mat n} (hN : Nᵀ = N) (s : ℝ) : Q 1 (-Complex.I * s) N ≠ 0 := by
  rw [Q_symm (isHermitian_of_transpose hN)]
  rw [Finset.prod_ne_zero_iff]
  intro i _ h
  have := congrArg Complex.re h
  simp at this

lemma Q_ne_zero_I {N : Mat n} (hN : Nᵀ = N) (s : ℝ) : Q (-Complex.I) s N ≠ 0 := by
  rw [Q_symm (isHermitian_of_transpose hN)]
  rw [Finset.prod_ne_zero_iff]
  intro i _ h
  have := congrArg Complex.im h
  simp at this

lemma continuous_Q (a : ℂ) {b : unitInterval × unitInterval → ℂ} (hb : Continuous b)
    {M : unitInterval × unitInterval → Mat n} (hM : Continuous M) :
    Continuous fun p => Q a (b p) (M p) := by
  unfold Q cx
  exact (continuous_const.add (hb.smul (hM.matrix_map Complex.continuous_ofReal))).matrix_det

/-! ### Arguments of products -/

lemma isArgLift_phase_sq_prod {ι : Type*} [Fintype ι] (z : unitInterval → ι → ℂ)
    (hc : ∀ i, Continuous fun t => z t i) (hs : ∀ t i, z t i ∈ Complex.slitPlane) :
    IsArgLift (fun t => phase (∏ i, z t i) ^ 2) (fun t => ∑ i, 2 * (z t i).arg) := by
  refine ⟨continuous_finset_sum _ fun i _ => continuous_const.mul ?_, fun t => ?_⟩
  · exact continuous_iff_continuousAt.2 fun t =>
      ContinuousAt.comp (f := fun t => z t i) (Complex.continuousAt_arg (hs t i))
        (hc i).continuousAt
  · show phase (∏ i, z t i) ^ 2 = Complex.exp (((∑ i, 2 * (z t i).arg : ℝ) : ℂ) * Complex.I)
    rw [phase_prod, ← Finset.prod_pow]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [phase_eq_exp (Complex.slitPlane_ne_zero (hs t i)), sq, ← Complex.exp_add]
    ring_nf

lemma isArgLift_const (w : ℂ) (hw : ‖w‖ = 1) :
    IsArgLift (fun _ : unitInterval => w) (fun _ => w.arg) := by
  refine ⟨continuous_const, fun _ => ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I w
  rw [hw, Complex.ofReal_one, one_mul] at h
  exact h.symm

lemma isArgLift_sq {f : unitInterval → ℂ} {θ : unitInterval → ℝ} (h : IsArgLift f θ) :
    IsArgLift (fun t => f t ^ 2) (fun t => 2 * θ t) := by
  refine ⟨continuous_const.mul h.1, fun t => ?_⟩
  show f t ^ 2 = Complex.exp (((2 * θ t : ℝ) : ℂ) * Complex.I)
  rw [h.2 t, sq, ← Complex.exp_add]
  push_cast
  ring_nf

/-- increments of any two lifts of the same function agree -/
lemma incr_eq {f : unitInterval → ℂ} {θ θ' : unitInterval → ℝ} (h : IsArgLift f θ)
    (h' : IsArgLift f θ') : θ 1 - θ 0 = θ' 1 - θ' 0 := by
  have hf : Continuous f := by
    have : f = fun t => Complex.exp ((θ t : ℂ) * Complex.I) := funext h.2
    rw [this]; exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp h.1).mul continuous_const)
  have h1 : ∀ t, ‖f t‖ = 1 := fun t => by
    rw [h.2 t, Complex.norm_exp_ofReal_mul_I]
  exact (argLift_exists_increment_unique hf h1).2 θ θ' h h'

end CZ13

namespace CZ13

variable {n : ℕ}

/-- Cayley chart regular at `Id`. -/
noncomputable def ncay (A : Mat n) : Mat n := J₀ n * (A - 1) * (A + 1)⁻¹

/-- Cayley chart on `Sp*`. -/
noncomputable def cay (A : Mat n) : Mat n := J₀ n * (A + 1) * (1 - A)⁻¹

lemma J_mul_J : J₀ n * J₀ n = -1 := J_squared (Fin n) ℝ

lemma J_mul_JT : J₀ n * (J₀ n)ᵀ = 1 := by
  rw [J_transpose, Matrix.mul_neg, J_mul_J, neg_neg]

lemma JT_mul_J : (J₀ n)ᵀ * J₀ n = 1 := by
  rw [J_transpose, Matrix.neg_mul, J_mul_J, neg_neg]

lemma ncay_one : ncay (1 : Mat n) = 0 := by simp [ncay]

lemma ncay_symm {A : Mat n} (hs : IsSymplectic A) (hd : (A + 1).det ≠ 0) :
    (ncay A)ᵀ = ncay A := by
  have hJ : Aᵀ * J₀ n * A = J₀ n := (SymplecticGroup.mem_iff').1 hs
  have hNu : IsUnit (A + 1 : Mat n).det := isUnit_iff_ne_zero.2 hd
  have hNt : IsUnit (A + 1 : Mat n)ᵀ :=
    (isUnit_iff_isUnit_det _).2 (by rw [det_transpose]; exact hNu)
  have hN : IsUnit (A + 1 : Mat n) := (isUnit_iff_isUnit_det _).2 hNu
  have h1 : ncay A * (A + 1) = J₀ n * (A - 1) := by
    simp only [ncay, Matrix.mul_assoc, nonsing_inv_mul _ hNu, Matrix.mul_one]
  have key : (A + 1)ᵀ * (ncay A)ᵀ * (A + 1) = (A + 1)ᵀ * ncay A * (A + 1) := by
    have h2 : (A + 1)ᵀ * (ncay A)ᵀ = (J₀ n * (A - 1))ᵀ := by
      rw [← transpose_mul, h1]
    rw [h2, Matrix.mul_assoc, h1]
    simp only [transpose_mul, J_transpose, transpose_add, transpose_one, transpose_sub]
    have e1 : (Aᵀ - 1) * -J₀ n * (A + 1) =
        -(Aᵀ * J₀ n * A) - Aᵀ * J₀ n + J₀ n * A + J₀ n := by
      simp only [sub_mul, mul_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
      abel
    have e2 : (Aᵀ + 1) * (J₀ n * (A - 1)) = Aᵀ * J₀ n * A - Aᵀ * J₀ n + J₀ n * A - J₀ n := by
      simp only [add_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [e1, e2, hJ]
    abel
  exact hNt.mul_left_cancel (hN.mul_right_cancel key)

lemma cay_symm {A : Mat n} (hA : A ∈ SpStar n) : (cay A)ᵀ = cay A := by
  obtain ⟨hs, hd⟩ := hA
  have hJ : Aᵀ * J₀ n * A = J₀ n := (SymplecticGroup.mem_iff').1 hs
  have hNu : IsUnit (1 - A : Mat n).det := isUnit_iff_ne_zero.2 hd
  have hNt : IsUnit (1 - A : Mat n)ᵀ :=
    (isUnit_iff_isUnit_det _).2 (by rw [det_transpose]; exact hNu)
  have hN : IsUnit (1 - A : Mat n) := (isUnit_iff_isUnit_det _).2 hNu
  have h1 : cay A * (1 - A) = J₀ n * (A + 1) := by
    simp only [cay, Matrix.mul_assoc, nonsing_inv_mul _ hNu, Matrix.mul_one]
  have key : (1 - A)ᵀ * (cay A)ᵀ * (1 - A) = (1 - A)ᵀ * cay A * (1 - A) := by
    have h2 : (1 - A)ᵀ * (cay A)ᵀ = (J₀ n * (A + 1))ᵀ := by
      rw [← transpose_mul, h1]
    rw [h2, Matrix.mul_assoc, h1]
    simp only [transpose_mul, J_transpose, transpose_add, transpose_one, transpose_sub]
    have e1 : (Aᵀ + 1) * -J₀ n * (1 - A) = -(Aᵀ * J₀ n) + Aᵀ * J₀ n * A - J₀ n + J₀ n * A := by
      simp only [add_mul, mul_sub, Matrix.mul_neg, Matrix.neg_mul, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
      abel
    have e2 : (1 - Aᵀ) * (J₀ n * (A + 1)) = J₀ n * A + J₀ n - Aᵀ * J₀ n * A - Aᵀ * J₀ n := by
      simp only [sub_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [e1, e2, hJ]
    abel
  exact hNt.mul_left_cancel (hN.mul_right_cancel key)

lemma det_J_ne_zero : (J₀ n).det ≠ 0 := by
  intro h
  have := congrArg det (J_mul_JT (n := n))
  rw [det_mul, h, zero_mul, det_one] at this
  exact zero_ne_one this

/-- `ρ̂²` in the chart regular at `Id`. -/
lemma rhoHat_sq_ncay {A : Mat n} (hd : (A + 1).det ≠ 0) :
    rhoHat A ^ 2 = phase (Q 1 (-Complex.I) (ncay A)) ^ 2 := by
  have hNu : IsUnit (A + 1).det := isUnit_iff_ne_zero.2 hd
  have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfac : (4 : ℂ) ^ n * complexLinearDet A = ((A + 1).det : ℂ) * Q 1 (-Complex.I) (ncay A) := by
    rw [complexLinearDet_mul_four_pow]
    have h1 : ncay A * (A + 1) = J₀ n * (A - 1) := by
      simp only [ncay, Matrix.mul_assoc, nonsing_inv_mul _ hNu, Matrix.mul_one]
    have hm : (A + 1).map (fun x : ℝ => (x : ℂ)) -
        Complex.I • (J₀ n * (A - 1)).map (fun x : ℝ => (x : ℂ)) =
        ((1 : ℂ) • (1 : Matrix _ _ ℂ) + (-Complex.I) • cx (ncay A)) * cx (A + 1) := by
      rw [one_smul, Matrix.add_mul, Matrix.one_mul, smul_mul_assoc, ← cx_mul, h1, neg_smul]
      abel
    rw [hm, det_mul, cx_det]
    unfold Q
    ring
  have hc : (A + 1).det / 4 ^ n ≠ 0 := div_ne_zero hd (pow_ne_zero _ (by norm_num))
  have hcl : complexLinearDet A = (((A + 1).det / 4 ^ n : ℝ) : ℂ) * Q 1 (-Complex.I) (ncay A) := by
    apply mul_left_cancel₀ h4
    rw [hfac]
    push_cast
    field_simp
  rw [show rhoHat A = phase (complexLinearDet A) from rfl, hcl, phase_real_mul_sq hc]

lemma det_negJ_ne_zero : (-J₀ n).det ≠ 0 := by
  intro h
  have : (-J₀ n * J₀ n).det = 1 := by
    rw [Matrix.neg_mul, J_mul_J, neg_neg, det_one]
  rw [det_mul, h, zero_mul] at this
  exact zero_ne_one this

/-- `ρ̂²` in the chart on `Sp*`. -/
lemma rhoHat_sq_cay {A : Mat n} (hA : A ∈ SpStar n) :
    rhoHat A ^ 2 = phase (Q (-Complex.I) 1 (cay A)) ^ 2 := by
  have hNu : IsUnit (1 - A).det := isUnit_iff_ne_zero.2 hA.2
  have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfac : (4 : ℂ) ^ n * complexLinearDet A =
      (((-J₀ n).det * (1 - A).det : ℝ) : ℂ) * Q (-Complex.I) 1 (cay A) := by
    rw [complexLinearDet_mul_four_pow]
    have h1 : -J₀ n * cay A * (1 - A) = A + 1 := by
      simp only [cay, Matrix.mul_assoc, nonsing_inv_mul _ hNu, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Matrix.neg_mul, J_mul_J, neg_neg, Matrix.one_mul]
    have h2 : -J₀ n * (1 - A) = J₀ n * (A - 1) := by
      simp only [Matrix.neg_mul, mul_sub, Matrix.mul_one]
      abel
    have hm : (A + 1).map (fun x : ℝ => (x : ℂ)) -
        Complex.I • (J₀ n * (A - 1)).map (fun x : ℝ => (x : ℂ)) =
        cx (-J₀ n) * ((-Complex.I) • (1 : Matrix _ _ ℂ) + (1 : ℂ) • cx (cay A)) * cx (1 - A) := by
      rw [one_smul, Matrix.mul_add, Matrix.add_mul, mul_smul_comm, Matrix.mul_one, smul_mul_assoc,
        ← cx_mul, ← cx_mul, ← cx_mul, h1, h2, neg_smul]
      abel
    rw [hm, det_mul, det_mul, cx_det, cx_det]
    unfold Q
    push_cast
    ring
  have hc : (-J₀ n).det * (1 - A).det / 4 ^ n ≠ 0 :=
    div_ne_zero (mul_ne_zero det_negJ_ne_zero hA.2) (pow_ne_zero _ (by norm_num))
  have hcl : complexLinearDet A =
      (((-J₀ n).det * (1 - A).det / 4 ^ n : ℝ) : ℂ) * Q (-Complex.I) 1 (cay A) := by
    apply mul_left_cancel₀ h4
    rw [hfac]
    push_cast
    field_simp
  rw [show rhoHat A = phase (complexLinearDet A) from rfl, hcl, phase_real_mul_sq hc]

/-- the eigenvalues of `ncay A` are nonzero on `Sp*` -/
lemma eig_ne_zero {A : Mat n} (hA : A ∈ SpStar n) (hd : (A + 1).det ≠ 0)
    (hN : (ncay A).IsHermitian) (i : Fin n ⊕ Fin n) : hN.eigenvalues i ≠ 0 := by
  have hdet : (ncay A).det ≠ 0 := by
    have h1 : (A - 1).det ≠ 0 := by
      rw [show A - 1 = -(1 - A) by abel, det_neg]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hA.2
    have h2 : ((A + 1)⁻¹).det ≠ 0 := by
      exact (isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hd)).ne_zero
    rw [ncay, det_mul, det_mul]
    exact mul_ne_zero (mul_ne_zero det_J_ne_zero h1) h2
  rw [hN.det_eq_prod_eigenvalues] at hdet
  have := (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ _)
  simpa using this

/-- the chart on `Sp*` is the conjugated inverse of the chart at `Id` -/
lemma cay_eq_conj {A : Mat n} (hA : A ∈ SpStar n) (hd : (A + 1).det ≠ 0)
    (hN : (ncay A).IsHermitian) :
    cay A = (J₀ n * evU hN) * diagonal (fun i => (hN.eigenvalues i)⁻¹) * (J₀ n * evU hN)ᵀ := by
  obtain ⟨hNd, hUU, hUU'⟩ := evU_spec hN
  set U := evU hN
  set M : Mat n := J₀ n * ncay A * (J₀ n)ᵀ with hM
  have hNu : IsUnit (A + 1).det := isUnit_iff_ne_zero.2 hd
  have hOu : IsUnit (1 - A).det := isUnit_iff_ne_zero.2 hA.2
  have hc : cay A * M = 1 := by
    have e2 : (1 - A)⁻¹ * (A - 1) = -1 := by
      rw [show A - 1 = -(1 - A) by abel, Matrix.mul_neg, nonsing_inv_mul _ hOu]
    have e3 : (A + 1) * (A + 1)⁻¹ = 1 := mul_nonsing_inv _ hNu
    have : cay A * M = J₀ n * (A + 1) * ((1 - A)⁻¹ * ((J₀ n * J₀ n) * (A - 1))) *
        (A + 1)⁻¹ * (J₀ n)ᵀ := by
      simp only [hM, cay, ncay, Matrix.mul_assoc]
    rw [this, J_mul_J, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, e2, neg_neg, Matrix.mul_one,
      Matrix.mul_assoc (J₀ n) (A + 1) (A + 1)⁻¹, e3, Matrix.mul_one, J_mul_JT]
  have hMd : M = (J₀ n * U) * diagonal hN.eigenvalues * (J₀ n * U)ᵀ := by
    rw [hM]
    conv_lhs => rw [hNd]
    rw [transpose_mul]
    simp only [Matrix.mul_assoc]
  have hp : (J₀ n * U) * diagonal (fun i => (hN.eigenvalues i)⁻¹) * (J₀ n * U)ᵀ * M = 1 := by
    have hJU : (J₀ n * U)ᵀ * (J₀ n * U) = 1 := by
      rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (J₀ n)ᵀ, JT_mul_J, Matrix.one_mul,
        hUU]
    have hD : diagonal (fun i => (hN.eigenvalues i)⁻¹) * diagonal hN.eigenvalues = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext i
      exact inv_mul_cancel₀ (eig_ne_zero hA hd hN i)
    have hJU' : (J₀ n * U) * (J₀ n * U)ᵀ = 1 := by
      rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hUU', Matrix.one_mul, J_mul_JT]
    rw [hMd]
    calc (J₀ n * U) * diagonal (fun i => (hN.eigenvalues i)⁻¹) * (J₀ n * U)ᵀ *
          ((J₀ n * U) * diagonal hN.eigenvalues * (J₀ n * U)ᵀ)
        = (J₀ n * U) * (diagonal (fun i => (hN.eigenvalues i)⁻¹) *
            ((J₀ n * U)ᵀ * (J₀ n * U)) * diagonal hN.eigenvalues) * (J₀ n * U)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJU, Matrix.mul_one, hD, Matrix.mul_one, hJU']
  have i1 := Matrix.inv_eq_left_inv hc
  have i2 := Matrix.inv_eq_left_inv hp
  rw [← i1, i2]

/-- `cay` of a diagonal matrix -/
lemma cay_diagonal (w : Fin n ⊕ Fin n → ℝ) :
    ∃ e, cay (diagonal w) = J₀ n * diagonal e := by
  refine ⟨(w + 1) * Ring.inverse (1 - w), ?_⟩
  rw [cay, Matrix.mul_assoc, ← diagonal_one, diagonal_add, diagonal_sub, inv_diagonal,
    diagonal_mul_diagonal]
  rfl

lemma cay_W {W : Mat n} (hW : W = Wplus n ∨ W = Wminus n) : ∃ e, cay W = J₀ n * diagonal e := by
  rcases hW with rfl | rfl
  · refine cay_diagonal (fun _ => -1) |>.imp fun e he => ?_
    rw [← he]; congr 1
    ext i j; by_cases h : i = j <;> simp [Wplus, diagonal, one_apply, h]
  · exact cay_diagonal _

/-- along a ray through a matrix `J₀ D` the phase squared is `1` -/
lemma phase_sq_Q_JD (e : Fin n ⊕ Fin n → ℝ) (s : ℝ) (hne : Q (-Complex.I) s (J₀ n * diagonal e) ≠ 0) :
    phase (Q (-Complex.I) s (J₀ n * diagonal e)) ^ 2 = 1 := by
  set X := J₀ n * diagonal e
  set P : Mat n := diagonal (Sum.elim (fun _ => (1 : ℝ)) (fun _ => -1))
  have hPP : P * P = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; rcases i with i | i <;> simp
  have hPXP : P * X * P = -X := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [P, X, Matrix.J, diagonal_mul, mul_diagonal, fromBlocks, Matrix.neg_apply]
  -- `z = Q (-I) s X` equals `Q (-I) (-s) X`
  have h1 : Q (-Complex.I) s X = Q (-Complex.I) (-s) X := by
    unfold Q
    have hdet : (cx P).det * (cx P).det = 1 := by
      rw [← det_mul, ← cx_mul, hPP, cx_one, det_one]
    have hm : cx P * ((-Complex.I) • (1 : Matrix _ _ ℂ) + (s : ℂ) • cx X) * cx P =
        (-Complex.I) • (1 : Matrix _ _ ℂ) + (-(s : ℂ)) • cx X := by
      rw [Matrix.mul_add, Matrix.add_mul, mul_smul_comm, Matrix.mul_one, smul_mul_assoc,
        ← cx_mul, hPP, cx_one, mul_smul_comm, smul_mul_assoc, ← cx_mul, ← cx_mul, hPXP]
      simp only [cx_eq, map_neg]
      simp only [neg_smul, smul_neg]
    have := congrArg det hm
    rw [det_mul, det_mul] at this
    rw [← this]
    linear_combination (-(((-Complex.I) • (1 : Matrix _ _ ℂ) + (s : ℂ) • cx X).det)) * hdet
  -- complex conjugation sends `Q (-I) s X` to `Q (-I) (-s) X`
  have h2 : (starRingEnd ℂ) (Q (-Complex.I) s X) = Q (-Complex.I) (-s) X := by
    unfold Q
    rw [RingHom.map_det]
    have hm : (starRingEnd ℂ).mapMatrix ((-Complex.I) • (1 : Matrix _ _ ℂ) + (s : ℂ) • cx X) =
        -((-Complex.I) • (1 : Matrix _ _ ℂ) + (-(s : ℂ)) • cx X) := by
      ext i j
      by_cases h : i = j
      · subst h; simp; ring
      · simp [one_apply, h]
    rw [hm, det_neg]
    simp
  have hreal : Q (-Complex.I) s X = ((Q (-Complex.I) s X).re : ℂ) := by
    exact (Complex.conj_eq_iff_re.1 (h2.trans h1.symm)).symm
  rw [hreal]
  apply phase_real_sq
  intro h0
  apply hne
  rw [hreal, h0, Complex.ofReal_zero]

end CZ13

namespace CZ14

open CZ13

variable {n : ℕ}

abbrev Vec (n : ℕ) := Fin n ⊕ Fin n → ℂ

/-- the complexified matrix as an endomorphism -/
noncomputable def fA (A : Mat n) : Module.End ℂ (Vec n) := Matrix.toLin' (cx A)

/-- the complex bilinear symplectic pairing `ω(v, w) = v ⬝ J₀ w` -/
noncomputable def ω (n : ℕ) : LinearMap.BilinForm ℂ (Vec n) := Matrix.toBilin' (cx (J₀ n))

lemma ω_apply (v w : Vec n) : ω n v w = v ⬝ᵥ (cx (J₀ n) *ᵥ w) := Matrix.toBilin'_apply' _ _ _

lemma fA_apply (A : Mat n) (v : Vec n) : fA A v = cx A *ᵥ v := Matrix.toLin'_apply _ _

lemma cx_transpose (M : Mat n) : cx Mᵀ = (cx M)ᵀ := by ext i j; rfl

lemma ω_fA {A : Mat n} (hs : IsSymplectic A) (v w : Vec n) :
    ω n (fA A v) (fA A w) = ω n v w := by
  have hJ : Aᵀ * J₀ n * A = J₀ n := (SymplecticGroup.mem_iff').1 hs
  have hc : (cx A)ᵀ * cx (J₀ n) * cx A = cx (J₀ n) := by
    rw [← cx_transpose, ← cx_mul, ← cx_mul, hJ]
  rw [ω_apply, ω_apply, fA_apply, fA_apply, mulVec_mulVec, dotProduct_mulVec,
    ← vecMul_transpose, vecMul_vecMul, dotProduct_mulVec, ← Matrix.mul_assoc, hc]

/-- `ω (v, (1 - μ f)^j x) = ω ((f - μ)^j v, f^j x)` -/
lemma ω_shift {A : Mat n} (hs : IsSymplectic A) (μ : ℂ) (j : ℕ) (v x : Vec n) :
    ω n v (aeval (fA A) ((1 - C μ * X) ^ j) x) =
      ω n (((fA A - μ • 1) ^ j) v) (((fA A) ^ j) x) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    have hcomm : aeval (fA A) ((1 - C μ * X) ^ (j + 1)) =
        aeval (fA A) ((1 - C μ * X) ^ j) * (1 - μ • fA A) := by
      rw [pow_succ, map_mul]
      congr 1
      simp [Algebra.smul_def]
    rw [hcomm, Module.End.mul_apply, ih]
    set u := ((fA A - μ • 1) ^ j) v
    have hpc : ((fA A) ^ j) ((1 - μ • fA A) x) = (1 - μ • fA A) (((fA A) ^ j) x) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply]
      congr 1
      exact ((Commute.one_right _).sub_right ((Commute.refl _).smul_right μ)).pow_left j |>.eq
    rw [hpc, pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
    set z := ((fA A) ^ j) x
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, map_sub, map_smul,
      LinearMap.sub_apply, LinearMap.smul_apply]
    rw [← ω_fA hs u z]

lemma coprime_lin {μ ν : ℂ} (h : μ * ν ≠ 1) : IsCoprime (X - C ν) (1 - C μ * X) := by
  have h1 : (1 - μ * ν) ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  refine ⟨C (μ / (1 - μ * ν)), C (1 / (1 - μ * ν)), ?_⟩
  have e : μ / (1 - μ * ν) * ν = 1 / (1 - μ * ν) - 1 := by field_simp; ring
  have e2 : 1 / (1 - μ * ν) * μ = μ / (1 - μ * ν) := by ring
  calc C (μ / (1 - μ * ν)) * (X - C ν) + C (1 / (1 - μ * ν)) * (1 - C μ * X)
      = C (μ / (1 - μ * ν)) * X - C (μ / (1 - μ * ν) * ν) + C (1 / (1 - μ * ν)) -
          C (1 / (1 - μ * ν) * μ) * X := by simp only [map_mul]; ring
    _ = 1 := by rw [e, e2, map_sub, map_one]; ring

/-- generalized eigenvectors for eigenvalues with `μ ν ≠ 1` are `ω`-orthogonal -/
lemma ω_gen_eq_zero {A : Mat n} (hs : IsSymplectic A) {μ ν : ℂ} (h : μ * ν ≠ 1) {v w : Vec n}
    (hv : v ∈ (fA A).maxGenEigenspace μ) (hw : w ∈ (fA A).maxGenEigenspace ν) :
    ω n v w = 0 := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hw
  obtain ⟨a, b, hab⟩ := ((coprime_lin h).pow (m := m) (n := k))
  have hP : aeval (fA A) ((X - C ν) ^ m) = (fA A - ν • 1) ^ m := by
    simp [Algebra.smul_def]
  have hw' : w = aeval (fA A) ((1 - C μ * X) ^ k) (aeval (fA A) b w) := by
    have := congrArg (fun p => aeval (fA A) p w) hab
    simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.one_apply, hP, hm, map_zero, zero_add] at this
    calc w = aeval (fA A) b (aeval (fA A) ((1 - C μ * X) ^ k) w) := this.symm
      _ = _ := by
        rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  rw [hw', ω_shift hs, hk]
  simp

/-- generalized eigenvalue subspaces for a set of eigenvalues -/
noncomputable def genSum (A : Mat n) (P : ℂ → Prop) : Submodule ℂ (Vec n) :=
  ⨆ (μ : ℂ) (_ : P μ), (fA A).maxGenEigenspace μ

lemma genSum_isotropic {A : Mat n} (hs : IsSymplectic A) {P : ℂ → Prop}
    (hP : ∀ μ ν, P μ → P ν → μ * ν ≠ 1) :
    ∀ v ∈ genSum A P, ∀ w ∈ genSum A P, ω n v w = 0 := by
  intro v hv w hw
  have h1 : genSum A P ≤ LinearMap.ker ((ω n).flip w) := by
    refine iSup₂_le fun μ hμ x hx => ?_
    have h2 : genSum A P ≤ LinearMap.ker (ω n x) := by
      refine iSup₂_le fun ν hν y hy => ?_
      rw [LinearMap.mem_ker]
      exact ω_gen_eq_zero hs (hP μ ν hμ hν) hx hy
    rw [LinearMap.mem_ker]
    exact LinearMap.mem_ker.1 (h2 hw)
  exact LinearMap.mem_ker.1 (h1 hv)

lemma gen_eq_bot {A : Mat n} {μ : ℂ}
    (hdet : (A.map (fun x : ℝ => (x : ℂ)) - μ • 1).det ≠ 0) :
    (fA A).maxGenEigenspace μ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  have he : fA A - μ • (1 : Module.End ℂ (Vec n)) = Matrix.toLin' (cx A - μ • 1) := by
    rw [map_sub, map_smul, Matrix.toLin'_one]; rfl
  have hinj : Function.Injective ⇑(fA A - μ • (1 : Module.End ℂ (Vec n))) := by
    rw [he]
    exact (Matrix.mulVec_injective_iff_isUnit.2
      ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)))
  have hinjk : Function.Injective ⇑((fA A - μ • (1 : Module.End ℂ (Vec n))) ^ k) := by
    rw [Module.End.coe_pow]; exact hinj.iterate k
  rw [Submodule.mem_bot]
  exact hinjk (by rw [hk, map_zero])

lemma genSum_sup_eq_top {A : Mat n}
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → (A.map (fun x : ℝ => (x : ℂ)) - z • 1).det ≠ 0) :
    genSum A (fun μ => ‖μ‖ < 1) ⊔ genSum A (fun μ => 1 < ‖μ‖) = ⊤ := by
  rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top (fA A)]
  refine iSup_le fun μ => ?_
  rcases lt_trichotomy ‖μ‖ 1 with h | h | h
  · exact le_sup_of_le_left (le_iSup₂_of_le μ h le_rfl)
  · rw [gen_eq_bot (hcirc μ h)]; exact bot_le
  · exact le_sup_of_le_right (le_iSup₂_of_le μ h le_rfl)

lemma ω_ker_eq_bot : LinearMap.ker (ω n) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  have h1 : v ᵥ* cx (J₀ n) = 0 := by
    funext j
    have := LinearMap.congr_fun hv (Pi.single j 1)
    rw [ω_apply, dotProduct_mulVec, LinearMap.zero_apply] at this
    simpa using this
  have hJu : IsUnit (cx (J₀ n)) := by
    rw [isUnit_iff_isUnit_det, cx_det]
    exact isUnit_iff_ne_zero.2 (by
      have := congrArg det (J_squared (Fin n) ℝ)
      intro h0
      rw [det_mul, show (J₀ n).det = 0 by exact_mod_cast h0, zero_mul, det_neg, det_one] at this
      simp at this)
  rw [Submodule.mem_bot]
  exact (Matrix.vecMul_injective_iff_isUnit.2 hJu)
    (show v ᵥ* cx (J₀ n) = 0 ᵥ* cx (J₀ n) by rw [h1, zero_vecMul])

lemma finrank_le_of_isotropic {W : Submodule ℂ (Vec n)} (hW : ∀ v ∈ W, ∀ w ∈ W, ω n v w = 0) :
    finrank ℂ W ≤ n := by
  have h := (ω n).finrank_add_finrank_orthogonal' W
  have hle : W ≤ (ω n).orthogonal W := fun w hw v hv => hW v hv w hw
  have h2 := Submodule.finrank_mono hle
  have hk : (W ⊓ LinearMap.ker (ω n) : Submodule ℂ (Vec n)) = ⊥ := by
    rw [ω_ker_eq_bot, inf_bot_eq]
  rw [show (ω n).ker = LinearMap.ker (ω n) from rfl, hk, finrank_bot,
    Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h
  omega

/-- a hyperbolic symplectic matrix has an `n`-dimensional invariant, conjugation-stable,
`ω`-isotropic complex subspace -/
theorem exists_isotropic {A : Mat n} (hs : IsSymplectic A)
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → (A.map (fun x : ℝ => (x : ℂ)) - z • 1).det ≠ 0) :
    ∃ L : Submodule ℂ (Vec n), n ≤ finrank ℂ L ∧ (∀ v ∈ L, cx A *ᵥ v ∈ L) ∧
      (∀ v ∈ L, star v ∈ L) ∧ ∀ v ∈ L, ∀ w ∈ L, ω n v w = 0 := by
  set L := genSum A (fun μ => ‖μ‖ < 1)
  set U := genSum A (fun μ => 1 < ‖μ‖)
  have hL : ∀ v ∈ L, ∀ w ∈ L, ω n v w = 0 := genSum_isotropic hs fun μ ν hμ hν h => by
    have : ‖μ * ν‖ < 1 := by
      rw [norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hμ hν.le
    rw [h, norm_one] at this; exact lt_irrefl _ this
  have hU : ∀ v ∈ U, ∀ w ∈ U, ω n v w = 0 := genSum_isotropic hs fun μ ν hμ hν h => by
    have : 1 < ‖μ * ν‖ := by
      rw [norm_mul]; exact one_lt_mul_of_lt_of_le hμ hν.le
    rw [h, norm_one] at this; exact lt_irrefl _ this
  have hdimL := finrank_le_of_isotropic hL
  have hdimU := finrank_le_of_isotropic hU
  have htop := genSum_sup_eq_top hcirc
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq L U
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
    Fintype.card_fin] at hsum
  refine ⟨L, by omega, ?_, ?_, hL⟩
  · -- invariance
    have : L ≤ L.comap (fA A) := by
      refine iSup₂_le fun μ hμ v hv => ?_
      rw [Submodule.mem_comap]
      refine le_iSup₂_of_le (f := fun μ (_ : ‖μ‖ < 1) => (fA A).maxGenEigenspace μ) μ hμ le_rfl ?_
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
      refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
      rw [← Module.End.mul_apply, ← ((Commute.refl (fA A)).sub_right
        ((Commute.one_right _).smul_right μ)).pow_right k |>.eq, Module.End.mul_apply, hk, map_zero]
    intro v hv
    have := this hv
    rwa [Submodule.mem_comap, fA_apply] at this
  · -- conjugation
    have hstar : ∀ v : Vec n, fA A (star v) = star (fA A v) := fun v => by
      rw [fA_apply, fA_apply, star_mulVec, ← vecMul_transpose]
      congr 1
      ext i j
      simp [conjTranspose_apply]
    let L' : Submodule ℂ (Vec n) :=
      { carrier := {v | star v ∈ L}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, star_add] at *; exact L.add_mem ha hb
        zero_mem' := by simp
        smul_mem' := fun c v hv => by
          simp only [Set.mem_setOf_eq, star_smul] at *; exact L.smul_mem _ hv }
    have : L ≤ L' := by
      refine iSup₂_le fun μ hμ v hv => ?_
      show star v ∈ L
      refine le_iSup₂_of_le (f := fun μ (_ : ‖μ‖ < 1) => (fA A).maxGenEigenspace μ)
        (star μ) (by rwa [norm_star]) le_rfl ?_
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
      refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
      have key : ∀ j (x : Vec n), ((fA A - star μ • (1 : Module.End ℂ (Vec n))) ^ j) (star x) =
          star (((fA A - μ • (1 : Module.End ℂ (Vec n))) ^ j) x) := by
        intro j
        induction j with
        | zero => intro x; simp
        | succ j ih =>
          intro x
          have h1 : (fA A - star μ • (1 : Module.End ℂ (Vec n))) (star x) =
              star ((fA A - μ • (1 : Module.End ℂ (Vec n))) x) := by
            simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hstar,
              star_sub, star_smul]
          rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, h1, ih]
      rw [key, hk, star_zero]
    exact fun v hv => this hv

end CZ14

namespace CZ14

open CZ13

variable {n : ℕ}

lemma dot_mulVec_mulVec (P Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (x y : Vec n) :
    (P *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ ((Pᵀ * Q) *ᵥ y) := by
  rw [dotProduct_mulVec, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul]

lemma star_cx_mulVec (B : Mat n) (u : Vec n) : star (cx B *ᵥ u) = cx B *ᵥ star u := by
  rw [star_mulVec, ← vecMul_transpose]
  congr 1
  ext i j
  simp [conjTranspose_apply]

/-- the diagonal hermitian form `∑ ν_i |y_i|²` -/
noncomputable def hform (ν : Fin n ⊕ Fin n → ℝ) (y : Vec n) : ℝ := ∑ i, ν i * ‖y i‖ ^ 2

lemma hform_eq (ν : Fin n ⊕ Fin n → ℝ) (y : Vec n) :
    star y ⬝ᵥ (cx (diagonal ν) *ᵥ y) = (hform ν y : ℂ) := by
  have hd : cx (diagonal ν) = diagonal (fun i => (ν i : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [diagonal, h]
  rw [hd, hform, dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal, Pi.star_apply, ← Complex.conj_mul']
  simp only [RCLike.star_def]
  ring

lemma det_ne_of_hcirc {A : Mat n}
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → (A.map (fun x : ℝ => (x : ℂ)) - z • 1).det ≠ 0) (c : ℝ)
    (hc : ‖(c : ℂ)‖ = 1) : (A - c • 1).det ≠ 0 := by
  have h := hcirc c hc
  have e : A.map (fun x : ℝ => (x : ℂ)) - (c : ℂ) • 1 = cx (A - c • 1) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [one_apply, hij]
  rw [e, cx_det] at h
  exact_mod_cast h

lemma finrank_pos_span (ν : Fin n ⊕ Fin n → ℝ) (p : ℝ → Prop) [DecidablePred p] :
    finrank ℂ (Submodule.span ℂ (Set.range fun j : {j // p (ν j)} => (Pi.single (j : Fin n ⊕ Fin n) (1 : ℂ) : Vec n))) =
      (Finset.univ.filter fun i => p (ν i)).card := by
  have hli : LinearIndependent ℂ (fun j : {j // p (ν j)} => (Pi.single (j : Fin n ⊕ Fin n) (1 : ℂ) : Vec n)) := by
    have := (Pi.basisFun ℂ (Fin n ⊕ Fin n)).linearIndependent.comp
      (Subtype.val : {j // p (ν j)} → Fin n ⊕ Fin n) Subtype.val_injective
    convert this using 1
    funext j
    simp [Pi.basisFun_apply]
  rw [finrank_span_eq_card hli, Fintype.card_subtype]

lemma span_le_zero (ν : Fin n ⊕ Fin n → ℝ) (p : ℝ → Prop) [DecidablePred p] {y : Vec n}
    (hy : y ∈ Submodule.span ℂ (Set.range fun j : {j // p (ν j)} => (Pi.single (j : Fin n ⊕ Fin n) (1 : ℂ) : Vec n))) :
    ∀ i, ¬ p (ν i) → y i = 0 := by
  let Z : Submodule ℂ (Vec n) := ⨅ (i : Fin n ⊕ Fin n) (_ : ¬ p (ν i)), LinearMap.ker (LinearMap.proj i)
  have hle : Submodule.span ℂ (Set.range fun j : {j // p (ν j)} => (Pi.single (j : Fin n ⊕ Fin n) (1 : ℂ) : Vec n)) ≤ Z := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simp only [SetLike.mem_coe, Z, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
    intro i hi
    have : i ≠ (j : Fin n ⊕ Fin n) := fun h => hi (h ▸ j.2)
    simp [Pi.single_apply, this]
  intro i hi
  have := hle hy
  simp only [Z, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply] at this
  exact this i hi

/-- if `hform` vanishes on `W` and has a strict sign on `P \ {0}`, then `P ⊓ W = ⊥` and the
dimensions add up to at most `2n` -/
lemma card_add_le {W P : Submodule ℂ (Vec n)} (hP : ∀ y ∈ P, ∀ y' ∈ W, y = y' → y = 0) :
    finrank ℂ P + finrank ℂ W ≤ n + n := by
  have hinf : P ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_bot]
    exact hP y hy.1 y hy.2 rfl
  have h := Submodule.finrank_sup_add_finrank_inf_eq P W
  rw [hinf, finrank_bot, add_zero] at h
  have h2 := Submodule.finrank_le (P ⊔ W)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h2
  omega

end CZ14

open CZ13 CZ14 in
/-- for a hyperbolic symplectic `A`, the symmetric matrix `J₀ (A - 1) (A + 1)⁻¹` has signature `0` -/
theorem CZ14.signature_zero {n : ℕ} (A : Mat n) (hs : IsSymplectic A)
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → (A.map (fun x : ℝ => (x : ℂ)) - z • 1).det ≠ 0)
    (hN : (J₀ n * (A - 1) * (A + 1)⁻¹).IsHermitian) :
    signature (J₀ n * (A - 1) * (A + 1)⁻¹) hN = 0 := by
  have hd1 : (A + 1).det ≠ 0 := by
    have := det_ne_of_hcirc hcirc (-1) (by simp)
    rwa [neg_smul, one_smul, sub_neg_eq_add] at this
  have hd0 : (1 - A).det ≠ 0 := by
    have := det_ne_of_hcirc hcirc 1 (by simp)
    rw [one_smul] at this
    rw [show (1 : Mat n) - A = -(A - 1) by abel, det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) this
  have hSp : A ∈ SpStar n := ⟨hs, hd0⟩
  have hN' : (ncay A).IsHermitian := hN
  obtain ⟨hNd, hUU, hUU'⟩ := evU_spec hN'
  set ν := hN'.eigenvalues with hν
  have hν0 : ∀ i, ν i ≠ 0 := eig_ne_zero hSp hd1 hN'
  obtain ⟨L, hLdim, hLinv, hLstar, hLiso⟩ := exists_isotropic hs hcirc
  set U := evU hN'
  -- the subspace `W = Uᵀ (A + 1) L`
  set M : Mat n := Uᵀ * (A + 1) with hM
  have hMu : IsUnit (cx M) := by
    rw [isUnit_iff_isUnit_det, cx_det]
    refine isUnit_iff_ne_zero.2 ?_
    have hU : U.det ≠ 0 := by
      intro h0
      have := congrArg det hUU
      rw [det_mul, det_transpose, h0, zero_mul, det_one] at this
      exact zero_ne_one this
    rw [hM, det_mul, det_transpose]
    exact_mod_cast mul_ne_zero hU hd1
  have hMinj : Function.Injective (Matrix.toLin' (cx M)) := by
    intro a b h
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at h
    exact Matrix.mulVec_injective_iff_isUnit.2 hMu h
  set W := L.map (Matrix.toLin' (cx M))
  have hWdim : n ≤ finrank ℂ W := by
    rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hMinj L)]
    exact hLdim
  -- the form vanishes on `W`
  have hN1 : ncay A * (A + 1) = J₀ n * (A - 1) := by
    simp only [ncay, Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd1),
      Matrix.mul_one]
  have hMDM : Mᵀ * (diagonal ν * M) = (A + 1)ᵀ * (J₀ n * (A - 1)) := by
    rw [hM, transpose_mul, transpose_transpose, ← hN1, hNd]
    simp only [Matrix.mul_assoc]
  have hW0 : ∀ y ∈ W, hform ν y = 0 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Matrix.toLin'_apply]
    have h1 := hform_eq ν (cx M *ᵥ u)
    have key : star (cx M *ᵥ u) ⬝ᵥ (cx (diagonal ν) *ᵥ (cx M *ᵥ u)) =
        (cx (A + 1) *ᵥ star u) ⬝ᵥ (cx (J₀ n) *ᵥ (cx (A - 1) *ᵥ u)) := by
      rw [star_cx_mulVec, mulVec_mulVec, mulVec_mulVec, dot_mulVec_mulVec, dot_mulVec_mulVec]
      simp only [← cx_transpose, ← cx_mul, hMDM]
    rw [key] at h1
    have hx : cx (A + 1) *ᵥ star u ∈ L := by
      rw [cx_eq, map_add, map_one, add_mulVec, one_mulVec]
      exact L.add_mem (hLinv _ (hLstar u hu)) (hLstar u hu)
    have hy : cx (A - 1) *ᵥ u ∈ L := by
      rw [cx_eq, map_sub, map_one, sub_mulVec, one_mulVec]
      exact L.sub_mem (hLinv u hu) hu
    have := hLiso _ hx _ hy
    rw [ω_apply] at this
    rw [this] at h1
    exact_mod_cast h1.symm
  -- positive and negative parts
  set Pp := Submodule.span ℂ (Set.range fun j : {j // 0 < ν j} =>
    (Pi.single (j : Fin n ⊕ Fin n) (1 : ℂ) : Vec n))
  set Pn := Submodule.span ℂ (Set.range fun j : {j // ν j < 0} =>
    (Pi.single (j : Fin n ⊕ Fin n) (1 : ℂ) : Vec n))
  have hp : finrank ℂ Pp + finrank ℂ W ≤ n + n := by
    refine card_add_le fun y hy y' hy' hyy => ?_
    subst hyy
    by_contra hne
    have hz := span_le_zero ν (fun x => 0 < x) hy
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra h; push_neg at h; exact hne (funext h)
    have hpos : 0 < hform ν y := by
      refine Finset.sum_pos' (fun k _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
      · by_cases hk : 0 < ν k
        · positivity
        · rw [hz k hk, norm_zero]; simp
      · have hik : 0 < ν i := by by_contra h; exact hi (hz i h)
        have : 0 < ‖y i‖ := norm_pos_iff.2 hi
        positivity
    rw [hW0 y hy'] at hpos; exact lt_irrefl _ hpos
  have hq : finrank ℂ Pn + finrank ℂ W ≤ n + n := by
    refine card_add_le fun y hy y' hy' hyy => ?_
    subst hyy
    by_contra hne
    have hz := span_le_zero ν (fun x => x < 0) hy
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra h; push_neg at h; exact hne (funext h)
    have hneg : hform ν y < 0 := by
      have : 0 < ∑ k, -(ν k * ‖y k‖ ^ 2) := by
        refine Finset.sum_pos' (fun k _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
        · by_cases hk : ν k < 0
          · have : 0 ≤ ‖y k‖ ^ 2 := by positivity
            nlinarith
          · rw [hz k hk, norm_zero]; simp
        · have hik : ν i < 0 := by by_contra h; exact hi (hz i h)
          have : 0 < ‖y i‖ ^ 2 := by have := norm_pos_iff.2 hi; positivity
          nlinarith
      rw [Finset.sum_neg_distrib] at this
      unfold hform; linarith
    rw [hW0 y hy'] at hneg; exact lt_irrefl _ hneg
  rw [finrank_pos_span ν (fun x => 0 < x)] at hp
  rw [finrank_pos_span ν (fun x => x < 0)] at hq
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n ⊕ Fin n))) (fun i => 0 < ν i)
  have hfilt : (Finset.univ.filter fun i => ¬ 0 < ν i) = Finset.univ.filter fun i => ν i < 0 := by
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · intro h; exact lt_of_le_of_ne (not_lt.1 h) (hν0 i)
    · intro h; exact not_lt.2 h.le
  rw [hfilt, Finset.card_univ, Fintype.card_sum, Fintype.card_fin] at htot
  show ((Finset.univ.filter fun i => 0 < ν i).card : ℤ) -
    ((Finset.univ.filter fun i => ν i < 0).card : ℤ) = 0
  omega

open ConleyZehnder

theorem solution {n : ℕ} (A : Mat n) (hA : IsSymplectic A)
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → (A.map (fun x : ℝ => (x : ℂ)) - z • 1).det ≠ 0)
    (hN : (J₀ n * (A - 1) * (A + 1)⁻¹).IsHermitian) :
    signature (J₀ n * (A - 1) * (A + 1)⁻¹) hN = 0 :=
  CZ14.signature_zero A hA hcirc hN
