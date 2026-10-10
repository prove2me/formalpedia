-- Prove2me | solution 1 for ConleyZehnder.spStar_rhoHat_lift_increment_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T17:13:46.792857+00:00
-- url     : https://prove2.me/submissions/8e10a9c4-47e8-4194-aa35-f7306af8034d

import Theorems.Thm_ConleyZehnder_argLift_exists_increment_unique
import Theorems.Thm_ConleyZehnder_complexLinearDet_mul_four_pow
import Theorems.Thm_ConleyZehnder_argLift_increment_eq_of_homotopy
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

open ConleyZehnder Matrix

namespace CZ72


section

variable {n : ℕ}

/-- complexified matrix -/
noncomputable abbrev cx (M : Mat n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  M.map (fun x : ℝ => (x : ℂ))

lemma cx_eq (M : Mat n) : cx M = (Complex.ofRealHom).mapMatrix M := rfl

lemma cx_mul (M N : Mat n) : cx (M * N) = cx M * cx N := by
  simp only [cx_eq, map_mul]

lemma cx_det (M : Mat n) : (cx M).det = (M.det : ℂ) := by
  rw [cx_eq, ← RingHom.map_det]; rfl

/-- Cayley-type matrix. -/
noncomputable def cay (A : Mat n) : Mat n := J₀ n * (A + 1) * (1 - A)⁻¹

noncomputable def V (M : Mat n) : ℂ := (cx M - Complex.I • 1).det

lemma V_ne_zero {M : Mat n} (hM : Mᵀ = M) : V M ≠ 0 := by
  have hprod : (cx M - Complex.I • 1) * (cx M + Complex.I • 1) = cx (Mᵀ * M + 1) := by
    rw [hM]
    have : cx (M * M + 1) = cx M * cx M + 1 := by
      rw [cx_eq, map_add, map_mul, map_one]; rfl
    rw [this]
    have hI : Complex.I • Complex.I • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) = -1 := by
      rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    rw [sub_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, Matrix.one_mul, Matrix.one_mul,
      mul_smul_comm, Matrix.mul_one, hI]
    abel
  have hpos : (Mᵀ * M + 1).PosDef := by
    have := posSemidef_conjTranspose_mul_self M
    rw [conjTranspose_eq_transpose_of_trivial] at this
    exact PosDef.posSemidef_add this PosDef.one
  intro h
  have := congrArg det hprod
  rw [det_mul, cx_det] at this
  unfold V at h
  rw [h, zero_mul] at this
  exact (ne_of_gt hpos.det_pos) (by exact_mod_cast this.symm)

lemma cay_symm {A : Mat n} (hA : A ∈ SpStar n) : (cay A)ᵀ = cay A := by
  obtain ⟨hs, hd⟩ := hA
  have hJ : Aᵀ * J₀ n * A = J₀ n := (SymplecticGroup.mem_iff').1 hs
  have hNu : IsUnit (1 - A : Mat n).det := isUnit_iff_ne_zero.2 hd
  have hNt : IsUnit (1 - A : Mat n)ᵀ := (isUnit_iff_isUnit_det _).2 (by rw [det_transpose]; exact hNu)
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

lemma factor {A : Mat n} (hA : A ∈ SpStar n) :
    (4 : ℂ) ^ n * complexLinearDet A = (((-J₀ n).det * (1 - A).det : ℝ) : ℂ) * V (cay A) := by
  rw [complexLinearDet_mul_four_pow]
  have hNu : IsUnit (1 - A).det := isUnit_iff_ne_zero.2 hA.2
  have hfac : cx (A + 1) - Complex.I • cx (J₀ n * (A - 1)) =
      cx (-J₀ n) * (cx (cay A) - Complex.I • 1) * cx (1 - A) := by
    have h1 : -J₀ n * cay A * (1 - A) = A + 1 := by
      simp only [cay, Matrix.mul_assoc, nonsing_inv_mul _ hNu, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Matrix.neg_mul, J_squared, neg_neg, Matrix.one_mul]
    have h2 : -J₀ n * (1 - A) = J₀ n * (A - 1) := by
      simp only [Matrix.neg_mul, mul_sub, Matrix.mul_one]
      abel
    have h3 : cx (-J₀ n) * (cx (cay A) - Complex.I • 1) * cx (1 - A) =
        cx (-J₀ n * cay A * (1 - A)) - Complex.I • cx (-J₀ n * (1 - A)) := by
      rw [cx_mul, cx_mul, cx_mul, Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm, Matrix.mul_one,
        smul_mul_assoc]
    rw [h3, h1, h2]
  show _ = _
  unfold V
  rw [show ((A + 1).map (fun x : ℝ => (x : ℂ))) = cx (A + 1) from rfl,
    show ((J₀ n * (A - 1)).map (fun x : ℝ => (x : ℂ))) = cx (J₀ n * (A - 1)) from rfl, hfac,
    det_mul, det_mul, cx_det, cx_det]
  push_cast
  ring

noncomputable def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

lemma norm_phase {z : ℂ} (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  rw [phase, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.2 hz)]

lemma phase_real_mul_sq {c : ℝ} (hc : c ≠ 0) (w : ℂ) : phase ((c : ℂ) * w) ^ 2 = phase w ^ 2 := by
  have hcc : ((|c| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.2 hc
  have h2 : ((c : ℂ) / ((|c| : ℝ) : ℂ)) ^ 2 = 1 := by
    rw [div_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs, div_self]
    exact_mod_cast pow_ne_zero 2 hc
  simp only [phase, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul]
  rw [show (c : ℂ) * w / (((|c| : ℝ) : ℂ) * ((‖w‖ : ℝ) : ℂ)) =
      ((c : ℂ) / ((|c| : ℝ) : ℂ)) * (w / ((‖w‖ : ℝ) : ℂ)) by
    rw [mul_div_mul_comm], mul_pow, h2, one_mul]

lemma det_negJ_ne_zero : (-J₀ n).det ≠ 0 := by
  intro h
  have : (-J₀ n * J₀ n).det = 1 := by
    rw [Matrix.neg_mul, J_squared, neg_neg, det_one]
  rw [det_mul, h, zero_mul] at this
  exact zero_ne_one this

lemma rhoHat_sq {A : Mat n} (hA : A ∈ SpStar n) : rhoHat A ^ 2 = phase (V (cay A)) ^ 2 := by
  have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hc : (-J₀ n).det * (1 - A).det / 4 ^ n ≠ 0 :=
    div_ne_zero (mul_ne_zero det_negJ_ne_zero hA.2) (pow_ne_zero _ (by norm_num))
  have hcl : complexLinearDet A =
      (((-J₀ n).det * (1 - A).det / 4 ^ n : ℝ) : ℂ) * V (cay A) := by
    apply mul_left_cancel₀ h4
    rw [factor hA]
    push_cast
    field_simp
  rw [show rhoHat A = phase (complexLinearDet A) from rfl, hcl, phase_real_mul_sq hc]

lemma isArgLift_sq {f : unitInterval → ℂ} {θ : unitInterval → ℝ} (h : IsArgLift f θ) :
    IsArgLift (fun t => f t ^ 2) (fun t => 2 * θ t) := by
  refine ⟨continuous_const.mul h.1, fun t => ?_⟩
  show f t ^ 2 = Complex.exp (((2 * θ t : ℝ) : ℂ) * Complex.I)
  rw [h.2 t, sq, ← Complex.exp_add]
  push_cast
  ring_nf

lemma continuous_cay {χ : C(unitInterval, Mat n)} (hχ : ∀ t, χ t ∈ SpStar n) :
    Continuous fun t => cay (χ t) := by
  have hinv : Continuous fun t => (1 - χ t)⁻¹ := by
    rw [continuous_iff_continuousAt]
    intro t
    refine ContinuousAt.comp (f := fun t => 1 - χ t) ?_ (by fun_prop)
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hχ t).2
  unfold cay
  fun_prop

lemma continuous_V : Continuous (V : Mat n → ℂ) := by
  unfold V cx
  exact (Continuous.matrix_map continuous_id Complex.continuous_ofReal |>.sub
    continuous_const).matrix_det

lemma symm_comb {X Y : Mat n} (hX : Xᵀ = X) (hY : Yᵀ = Y) (a b : ℝ) :
    (a • X + b • Y)ᵀ = a • X + b • Y := by
  rw [transpose_add, transpose_smul, transpose_smul, hX, hY]

end

end CZ72

open CZ72 in
theorem solution {n : ℕ} (χ χ' : C(unitInterval, Mat n))
    (hχ : ∀ t, χ t ∈ SpStar n) (hχ' : ∀ t, χ' t ∈ SpStar n)
    (h0 : χ 0 = χ' 0) (h1 : χ 1 = χ' 1) (θ θ' : unitInterval → ℝ)
    (hθ : IsArgLift (fun t => rhoHat (χ t)) θ)
    (hθ' : IsArgLift (fun t => rhoHat (χ' t)) θ') :
    θ 1 - θ 0 = θ' 1 - θ' 0 := by
  let G : unitInterval × unitInterval → Mat n := fun p =>
    (1 - (p.1 : ℝ)) • cay (χ p.2) + (p.1 : ℝ) • cay (χ' p.2)
  have hGc : Continuous G := by
    have c1 := continuous_cay hχ
    have c2 := continuous_cay hχ'
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (c1.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul (c2.comp continuous_snd))
  have hGs : ∀ p, (G p)ᵀ = G p := fun p =>
    symm_comb (cay_symm (hχ p.2)) (cay_symm (hχ' p.2)) _ _
  have hVne : ∀ p, V (G p) ≠ 0 := fun p => V_ne_zero (hGs p)
  have hVc : Continuous fun p => V (G p) := continuous_V.comp hGc
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => phase (V (G p)), by
      unfold phase
      exact hVc.div (Complex.continuous_ofReal.comp hVc.norm)
        (fun p => by exact_mod_cast norm_ne_zero_iff.2 (hVne p))⟩
  have hH1 : ∀ p, ‖H p‖ = 1 := fun p => norm_phase (hVne p)
  have hG0 : ∀ t, G (0, t) = cay (χ t) := fun t => by simp [G]
  have hG1 : ∀ t, G (1, t) = cay (χ' t) := fun t => by simp [G]
  have hHe : ∀ s (t : unitInterval), cay (χ t) = cay (χ' t) → H (s, t) = H (0, t) := by
    intro s t ht
    show phase (V (G (s, t))) = phase (V (G (0, t)))
    simp only [G, ht]
    congr 2
    simp only [Set.Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero, ← add_smul]
    ring_nf
    rw [one_smul]
  -- continuous arguments of the two phase paths
  have hu : Continuous fun t => H (0, t) := H.continuous.comp (continuous_const.prodMk continuous_id)
  have hu' : Continuous fun t => H (1, t) :=
    H.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨φ, hφ⟩ := (argLift_exists_increment_unique hu (fun t => hH1 _)).1
  obtain ⟨φ', hφ'⟩ := (argLift_exists_increment_unique hu' (fun t => hH1 _)).1
  have hφφ' := argLift_increment_eq_of_homotopy H hH1
    (fun s => hHe s 0 (by rw [h0])) (fun s => hHe s 1 (by rw [h1])) φ φ' hφ hφ'
  -- squares
  have hsq : ∀ t, rhoHat (χ t) ^ 2 = H (0, t) ^ 2 := fun t => by
    rw [rhoHat_sq (hχ t)]; show _ = phase (V (G (0, t))) ^ 2; rw [hG0]
  have hsq' : ∀ t, rhoHat (χ' t) ^ 2 = H (1, t) ^ 2 := fun t => by
    rw [rhoHat_sq (hχ' t)]; show _ = phase (V (G (1, t))) ^ 2; rw [hG1]
  have e1 := (argLift_exists_increment_unique (f := fun t => H (0, t) ^ 2) (hu.pow 2)
    (fun t => by rw [norm_pow, hH1, one_pow])).2 _ _
    (by simpa only [hsq] using isArgLift_sq hθ) (isArgLift_sq hφ)
  have e2 := (argLift_exists_increment_unique (f := fun t => H (1, t) ^ 2) (hu'.pow 2)
    (fun t => by rw [norm_pow, hH1, one_pow])).2 _ _
    (by simpa only [hsq'] using isArgLift_sq hθ') (isArgLift_sq hφ')
  linarith
