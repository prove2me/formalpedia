-- Prove2me | solution 1 for ConleyZehnder.czValue_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T16:27:52.477962+00:00
-- url     : https://prove2.me/submissions/85ae26f6-3082-4078-8f00-cb98a0440ef3

import Theorems.Thm_ConleyZehnder_complexLinearDet_ne_zero
import Theorems.Thm_ConleyZehnder_argLift_exists_increment_unique
import Theorems.Thm_ConleyZehnder_spStar_exists_path_to_W
import Theorems.Thm_ConleyZehnder_spStar_rhoHat_lift_increment_eq

open ConleyZehnder Matrix

namespace CZ7

variable {n : ℕ}

theorem continuous_complexLinearDet : Continuous fun A : Mat n => complexLinearDet A := by
  have hC : Continuous (complexLinearPart : Mat n → Mat n) := by
    unfold complexLinearPart
    fun_prop
  unfold complexLinearDet
  refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.toBlocks₁₁,
    Matrix.toBlocks₂₁, Matrix.of_apply, smul_eq_mul]
  exact (Complex.continuous_ofReal.comp (hC.matrix_elem _ _)).add
    (continuous_const.mul (Complex.continuous_ofReal.comp (hC.matrix_elem _ _)))

/-- Along a path of symplectic matrices, `ρ̂` is continuous with values in `S¹`. -/
theorem rhoHat_path (χ : C(unitInterval, Mat n)) (hχ : ∀ t, IsSymplectic (χ t)) :
    Continuous (fun t => rhoHat (χ t)) ∧ ∀ t, ‖rhoHat (χ t)‖ = 1 := by
  have hd : Continuous fun t => complexLinearDet (χ t) :=
    continuous_complexLinearDet.comp χ.continuous
  have hne : ∀ t, complexLinearDet (χ t) ≠ 0 := fun t => complexLinearDet_ne_zero _ (hχ t)
  refine ⟨?_, fun t => ?_⟩
  · unfold rhoHat
    refine hd.div (Complex.continuous_ofReal.comp hd.norm) fun t => ?_
    exact_mod_cast (norm_ne_zero_iff.2 (hne t))
  · unfold rhoHat
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 (hne t))]

theorem rhoHat_one : rhoHat (1 : Mat n) = 1 := by
  have hC : complexLinearPart (1 : Mat n) = 1 := by
    unfold complexLinearPart
    rw [Matrix.mul_one, Matrix.J_squared, sub_neg_eq_add, ← two_smul ℝ (1 : Mat n), smul_smul]
    norm_num
  have hD : complexLinearDet (1 : Mat n) = 1 := by
    unfold complexLinearDet
    rw [hC, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]
    have h1 : (Matrix.of fun i j => (1 : Mat n) (Sum.inl i) (Sum.inl j)).map
        (fun x : ℝ => (x : ℂ)) = 1 := by
      ext i j; by_cases h : i = j <;> simp [h, one_apply]
    have h2 : (Matrix.of fun i j => (1 : Mat n) (Sum.inr i) (Sum.inl j)).map
        (fun x : ℝ => (x : ℂ)) = 0 := by
      ext i j; simp [one_apply]
    rw [h1, h2, smul_zero, add_zero, det_one]
  simp [rhoHat, hD]

/-- For a diagonal matrix the complex determinant of the `ℂ`-linear part is real, so `ρ̂² = 1`
wherever that determinant is nonzero. -/
theorem rhoHat_diagonal_sq (d : Fin n ⊕ Fin n → ℝ) (hne : complexLinearDet (diagonal d) ≠ 0) :
    rhoHat (diagonal d) ^ 2 = 1 := by
  have h21 : (complexLinearPart (diagonal d)).toBlocks₂₁ = 0 := by
    ext i j
    simp [complexLinearPart, toBlocks₂₁, Matrix.J, mul_apply, Fintype.sum_sum_type,
      diagonal_apply, fromBlocks]
  set X := (complexLinearPart (diagonal d)).toBlocks₁₁
  have hD : complexLinearDet (diagonal d) = ((X.det : ℝ) : ℂ) := by
    unfold complexLinearDet
    rw [h21, Matrix.map_zero _ (by simp), smul_zero, add_zero]
    exact (Complex.ofRealHom.map_det X).symm
  unfold rhoHat
  rw [hD] at hne ⊢
  have hr : X.det ≠ 0 := by exact_mod_cast hne
  rw [Complex.norm_real, div_pow, Real.norm_eq_abs, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    sq_abs, div_self]
  exact_mod_cast pow_ne_zero 2 hr

theorem rhoHat_W_sq (A : Mat n) (hA : IsSymplectic A) (hW : A = Wplus n ∨ A = Wminus n) :
    rhoHat A ^ 2 = 1 := by
  have hne := complexLinearDet_ne_zero A hA
  rcases hW with rfl | rfl
  · have : Wplus n = diagonal (fun _ => (-1 : ℝ)) := by
      unfold Wplus; ext i j; by_cases h : i = j <;> simp [h, one_apply, diagonal_apply]
    rw [this] at hne ⊢; exact rhoHat_diagonal_sq _ hne
  · exact rhoHat_diagonal_sq _ hne

/-- A continuous nowhere-vanishing real function on `[0, 1]` has the same sign at both ends. -/
theorem sign_const (g : unitInterval → ℝ) (hg : Continuous g) (hne : ∀ t, g t ≠ 0) :
    (0 < g 0 ↔ 0 < g 1) := by
  constructor
  · intro h0; by_contra h1; push_neg at h1
    obtain ⟨t, ht⟩ := intermediate_value_univ 1 0 hg ⟨h1, h0.le⟩
    exact hne t ht
  · intro h1; by_contra h0; push_neg at h0
    obtain ⟨t, ht⟩ := intermediate_value_univ 0 1 hg ⟨h0, h1.le⟩
    exact hne t ht

theorem det_one_sub_Wplus : 0 < (1 - Wplus n).det := by
  have : (1 : Mat n) - Wplus n = diagonal (fun _ => (2 : ℝ)) := by
    unfold Wplus; ext i j; by_cases h : i = j <;> simp [h, one_apply, diagonal_apply]; norm_num
  rw [this, det_diagonal]
  exact Finset.prod_pos fun _ _ => by norm_num

theorem det_one_sub_Wminus (hn : 0 < n) : (1 - Wminus n).det < 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : (1 : Mat (m + 1)) - Wminus (m + 1) = diagonal (fun i => 1 - Sum.elim
      (fun j : Fin (m + 1) => if j.val = 0 then (2 : ℝ) else -1)
      (fun j : Fin (m + 1) => if j.val = 0 then (1 / 2 : ℝ) else -1) i) := by
    unfold Wminus; ext i j; by_cases h : i = j <;> simp [h, one_apply, diagonal_apply]
  rw [this, det_diagonal, Fintype.prod_sum_type, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.val_zero, Fin.val_succ, if_true,
    Nat.succ_ne_zero, if_false]
  have hp : 0 < ∏ i : Fin m, (1 - (-1 : ℝ)) := Finset.prod_pos fun _ _ => by norm_num
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- Two extensions of the same `ψ(1)` through `Sp*` end at the same matrix `W±`. -/
theorem endpoint_eq (χ χ' : C(unitInterval, Mat n)) (hχ : ∀ t, χ t ∈ SpStar n)
    (hχ' : ∀ t, χ' t ∈ SpStar n) (h0 : χ 0 = χ' 0)
    (h1 : χ 1 = Wplus n ∨ χ 1 = Wminus n) (h1' : χ' 1 = Wplus n ∨ χ' 1 = Wminus n) :
    χ 1 = χ' 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext i j; rcases i with i | i <;> exact i.elim0
  have s := sign_const (fun t => (1 - χ t).det)
    (continuous_const.sub χ.continuous).matrix_det fun t => (hχ t).2
  have s' := sign_const (fun t => (1 - χ' t).det)
    (continuous_const.sub χ'.continuous).matrix_det fun t => (hχ' t).2
  simp only [h0] at s
  beta_reduce at s'
  have hp := det_one_sub_Wplus (n := n)
  have hm := det_one_sub_Wminus hn
  rcases h1 with e | e <;> rcases h1' with e' | e'
  · rw [e, e']
  · exfalso; rw [e] at s; rw [e'] at s'; linarith [s'.1 (s.2 hp)]
  · exfalso; rw [e] at s; rw [e'] at s'; linarith [s.1 (s'.2 hp)]
  · rw [e, e']

/-- Integrality: for any extension and lifts, `2(Δθ₁ + Δθ₂) ∈ 2πℤ`. -/
theorem integral (ψ χ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) (hχ : IsSpStarExtension ψ χ)
    (θ₁ θ₂ : unitInterval → ℝ) (h₁ : IsArgLift (fun t => rhoHat (ψ t)) θ₁)
    (h₂ : IsArgLift (fun t => rhoHat (χ t)) θ₂) :
    ∃ k : ℤ, 2 * ((θ₁ 1 - θ₁ 0) + (θ₂ 1 - θ₂ 0)) = 2 * Real.pi * k := by
  have a0 : Complex.exp ((θ₁ 0 : ℂ) * Complex.I) = 1 := by
    rw [← h₁.2 0]; simp only [hψ.2.1, rhoHat_one]
  have bc : Complex.exp ((θ₁ 1 : ℂ) * Complex.I) = Complex.exp ((θ₂ 0 : ℂ) * Complex.I) := by
    rw [← h₁.2 1, ← h₂.2 0]; simp only [hχ.1]
  have d2 : Complex.exp ((θ₂ 1 : ℂ) * Complex.I) ^ 2 = 1 := by
    rw [← h₂.2 1]; exact rhoHat_W_sq _ (hχ.2.1 1).1 hχ.2.2
  set S := 2 * ((θ₁ 1 - θ₁ 0) + (θ₂ 1 - θ₂ 0))
  have hS : Complex.exp ((S : ℂ) * Complex.I) = 1 := by
    have : (S : ℂ) * Complex.I = ((2 : ℕ) : ℂ) * ((θ₂ 1 : ℂ) * Complex.I) +
        ((2 : ℕ) : ℂ) * ((θ₁ 1 : ℂ) * Complex.I) - ((2 : ℕ) : ℂ) * ((θ₂ 0 : ℂ) * Complex.I) -
        ((2 : ℕ) : ℂ) * ((θ₁ 0 : ℂ) * Complex.I) := by
      simp only [S]; push_cast; ring
    rw [this, Complex.exp_sub, Complex.exp_sub, Complex.exp_add, Complex.exp_nat_mul,
      Complex.exp_nat_mul, Complex.exp_nat_mul, Complex.exp_nat_mul, a0, d2, bc]
    have : Complex.exp ((θ₂ 0 : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 hS
  refine ⟨k, ?_⟩
  have := congrArg Complex.im hk
  simpa [Complex.mul_im, mul_comm, mul_left_comm, mul_assoc] using this

end CZ7

theorem solution {n : ℕ} (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) :
    ∃! k : ℤ, IsCZValue ψ k := by
  have hψsymp : ∀ t, IsSymplectic (ψ t) := hψ.1
  obtain ⟨hc₁, hn₁⟩ := CZ7.rhoHat_path ψ hψsymp
  obtain ⟨⟨θ₁, h₁⟩, u₁⟩ := argLift_exists_increment_unique hc₁ hn₁
  obtain ⟨χ, hχ0, hχS, hχW⟩ := spStar_exists_path_to_W (ψ 1)
    ⟨hψsymp 1, hψ.2.2⟩
  have hext : IsSpStarExtension ψ χ := ⟨hχ0, hχS, hχW⟩
  obtain ⟨hc₂, hn₂⟩ := CZ7.rhoHat_path χ fun t => (hχS t).1
  obtain ⟨⟨θ₂, h₂⟩, -⟩ := argLift_exists_increment_unique hc₂ hn₂
  obtain ⟨k, hk⟩ := CZ7.integral ψ χ hψ hext θ₁ θ₂ h₁ h₂
  refine ⟨k, ⟨χ, hext, θ₁, θ₂, h₁, h₂, hk⟩, ?_⟩
  rintro k' ⟨χ', hext', θ₁', θ₂', h₁', h₂', hk'⟩
  have e₁ := u₁ θ₁ θ₁' h₁ h₁'
  have hend := CZ7.endpoint_eq χ χ' hχS hext'.2.1 (hχ0.trans hext'.1.symm) hχW hext'.2.2
  have e₂ := spStar_rhoHat_lift_increment_eq χ χ' hχS hext'.2.1
    (hχ0.trans hext'.1.symm) hend θ₂ θ₂' h₂ h₂'
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have : (2 * Real.pi) * (k' : ℝ) = (2 * Real.pi) * k := by rw [← hk', ← hk, e₁, e₂]
  exact_mod_cast (mul_left_cancel₀ hpi this)
