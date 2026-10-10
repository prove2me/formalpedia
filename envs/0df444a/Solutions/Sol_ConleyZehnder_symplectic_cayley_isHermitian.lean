-- Prove2me | solution 1 for ConleyZehnder.symplectic_cayley_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T23:29:24.191532+00:00
-- url     : https://prove2.me/submissions/c4b907b7-1875-496c-a8bb-431e2ac4fe4c

import Definitions.Def_ConleyZehnder_Setting
import Theorems.Thm_ConleyZehnder_argLift_exists_increment_unique
import Theorems.Thm_ConleyZehnder_complexLinearDet_mul_four_pow
import Theorems.Thm_ConleyZehnder_argLift_square_increment
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

open ConleyZehnder Matrix

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

open ConleyZehnder

theorem solution {n : ℕ} (A : Mat n) (hA : IsSymplectic A)
    (hd : (A + 1).det ≠ 0) :
    (J₀ n * (A - 1) * (A + 1)⁻¹).IsHermitian :=
  CZ13.isHermitian_of_transpose (CZ13.ncay_symm hA hd)
