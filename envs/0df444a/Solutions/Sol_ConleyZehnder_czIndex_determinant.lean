-- Prove2me | solution 1 for ConleyZehnder.czIndex_determinant
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T10:37:59.340167+00:00
-- url     : https://prove2.me/submissions/1b9de56f-e2c0-4f2a-93d3-8bf23922354d

import Theorems.Thm_ConleyZehnder_czValue_existsUnique

open ConleyZehnder Matrix

namespace CZ17

variable {n : ℕ}

lemma clp_diag_11 (d : Fin n ⊕ Fin n → ℝ) :
    (complexLinearPart (diagonal d)).toBlocks₁₁ =
      diagonal (fun j => (d (Sum.inl j) + d (Sum.inr j)) / 2) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [complexLinearPart, toBlocks₁₁, Matrix.J, mul_apply, Fintype.sum_sum_type,
      diagonal_apply, one_apply]
    ring
  · simp [complexLinearPart, toBlocks₁₁, Matrix.J, mul_apply, Fintype.sum_sum_type,
      diagonal_apply, hij, one_apply]

lemma clp_diag_21 (d : Fin n ⊕ Fin n → ℝ) :
    (complexLinearPart (diagonal d)).toBlocks₂₁ = 0 := by
  ext i j
  simp [complexLinearPart, toBlocks₂₁, Matrix.J, mul_apply, Fintype.sum_sum_type,
    diagonal_apply, one_apply]

lemma cld_diag (d : Fin n ⊕ Fin n → ℝ) :
    complexLinearDet (diagonal d) =
      ((∏ j, (d (Sum.inl j) + d (Sum.inr j)) / 2 : ℝ) : ℂ) := by
  rw [complexLinearDet, clp_diag_11, clp_diag_21]
  simp [diagonal_map, det_diagonal]

lemma rhoHat_of_real (r : ℝ) (hr : r ≠ 0) (A : Mat n) (h : complexLinearDet A = (r : ℂ)) :
    rhoHat A = ((Real.sign r : ℝ) : ℂ) := by
  rw [rhoHat, h, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne hr with h' | h'
  · rw [Real.sign_of_neg h', abs_of_neg h']
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hr)]
  · rw [Real.sign_of_pos h', abs_of_pos h']
    push_cast
    rw [div_self (by exact_mod_cast hr)]

lemma rhoHat_one : rhoHat (1 : Mat n) = 1 := by
  have h := rhoHat_of_real 1 one_ne_zero (diagonal (fun _ => (1 : ℝ)) : Mat n)
    (by rw [cld_diag]; norm_num)
  simpa [diagonal_one, Real.sign_one] using h

lemma Wplus_eq : Wplus n = diagonal (fun _ => (-1 : ℝ)) := by
  rw [Wplus, ← diagonal_one, diagonal_neg]

/-- At the endpoints `W±`: `ρ̂ = (-1)^n sign det(1 - A)`. -/
lemma rhoHat_W (A : Mat n) (hA : A = Wplus n ∨ A = Wminus n) :
    rhoHat A = (((-1 : ℝ) ^ n * Real.sign (1 - A).det : ℝ) : ℂ) := by
  rcases hA with rfl | rfl
  · rw [Wplus_eq]
    have hdet : (1 - diagonal (fun _ : Fin n ⊕ Fin n => (-1 : ℝ))).det = 2 ^ (2 * n) := by
      rw [← diagonal_one, diagonal_sub, det_diagonal]
      norm_num [Finset.prod_const, Fintype.card_sum]
      ring
    rw [hdet, Real.sign_of_pos (by positivity), mul_one,
      rhoHat_of_real ((-1) ^ n) (by simp) _ (by rw [cld_diag]; norm_num)]
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> simp [Real.sign_one, Real.sign_neg]
  · cases n with
    | zero =>
      rw [det_isEmpty, Real.sign_one, pow_zero, mul_one,
        rhoHat_of_real 1 one_ne_zero _ (by rw [Wminus, cld_diag]; simp)]
      simp [Real.sign_one]
    | succ m =>
      have hprod : (∏ j : Fin (m + 1),
          ((Sum.elim (fun j : Fin (m + 1) => if j.val = 0 then (2 : ℝ) else -1)
            (fun j : Fin (m + 1) => if j.val = 0 then (1 / 2 : ℝ) else -1) (Sum.inl j) +
           Sum.elim (fun j : Fin (m + 1) => if j.val = 0 then (2 : ℝ) else -1)
            (fun j : Fin (m + 1) => if j.val = 0 then (1 / 2 : ℝ) else -1) (Sum.inr j)) / 2))
          = 5 / 4 * (-1) ^ m := by
        rw [Fin.prod_univ_succ]
        simp [Fin.succ_ne_zero, Finset.prod_const]
        norm_num
      have hdet : (1 - Wminus (m + 1)).det = -(1 / 2) * 4 ^ m := by
        rw [Wminus, ← diagonal_one, diagonal_sub, det_diagonal, Fintype.prod_sum_type,
          Fin.prod_univ_succ, Fin.prod_univ_succ]
        simp [Fin.succ_ne_zero, Finset.prod_const]
        rw [show (4 : ℝ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
        norm_num
        ring
      have hr : (5 / 4 * (-1) ^ m : ℝ) ≠ 0 := by simp
      rw [hdet, Real.sign_of_neg (by have := pow_pos (show (0 : ℝ) < 4 by norm_num) m; nlinarith),
        rhoHat_of_real _ hr _ (by rw [Wminus, cld_diag, hprod])]
      rw [pow_succ]
      rcases neg_one_pow_eq_or ℝ m with h | h
      · rw [h, Real.sign_of_pos (by norm_num)]; push_cast; ring
      · rw [h, Real.sign_of_neg (by norm_num)]; push_cast; ring

lemma sign_det_const (χ : C(unitInterval, Mat n)) (hχ : ∀ t, (1 - χ t).det ≠ 0) :
    Real.sign (1 - χ 0).det = Real.sign (1 - χ 1).det := by
  set f : unitInterval → ℝ := fun t => (1 - χ t).det
  have hf : Continuous f := (continuous_const.sub χ.continuous).matrix_det
  have key : ∀ a b : unitInterval, f a < 0 → 0 < f b → False := by
    intro a b ha hb
    obtain ⟨c, hc⟩ := intermediate_value_univ a b hf ⟨ha.le, hb.le⟩
    exact hχ c hc
  show Real.sign (f 0) = Real.sign (f 1)
  rcases lt_or_gt_of_ne (hχ 0) with h0 | h0 <;> rcases lt_or_gt_of_ne (hχ 1) with h1 | h1
  · rw [Real.sign_of_neg h0, Real.sign_of_neg h1]
  · exact (key 0 1 h0 h1).elim
  · exact (key 1 0 h1 h0).elim
  · rw [Real.sign_of_pos h0, Real.sign_of_pos h1]

end CZ17

open CZ17 in
theorem solution {n : ℕ} (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) :
    (-1 : ℝ) ^ ((n : ℤ) - czIndex ψ) = Real.sign (1 - ψ 1).det := by
  have hex : ∃ k, IsCZValue ψ k := (czValue_existsUnique ψ hψ).exists
  have hk : IsCZValue ψ (czIndex ψ) := by
    rw [czIndex, dif_pos hex]; exact hex.choose_spec
  set k := czIndex ψ
  obtain ⟨χ, ⟨h0, hχ, hW⟩, θ₁, θ₂, ⟨-, h1⟩, ⟨-, h2⟩, hsum⟩ := hk
  -- sign of `det(1 - ·)` is the same at `ψ 1 = χ 0` and at `χ 1`
  have hs : Real.sign (1 - ψ 1).det = Real.sign (1 - χ 1).det := by
    rw [← h0]; exact sign_det_const χ (fun t => (hχ t).2)
  -- `exp(iπk) = ρ̂(χ 1)`
  have hexp : Complex.exp (((θ₁ 1 - θ₁ 0) + (θ₂ 1 - θ₂ 0) : ℝ) * Complex.I) = rhoHat (χ 1) := by
    have e10 : Complex.exp ((θ₁ 0 : ℂ) * Complex.I) = 1 := by
      rw [← show rhoHat (ψ 0) = _ from h1 0, hψ.2.1, rhoHat_one]
    have e12 : Complex.exp ((θ₁ 1 : ℂ) * Complex.I) = Complex.exp ((θ₂ 0 : ℂ) * Complex.I) := by
      rw [← show rhoHat (ψ 1) = _ from h1 1, ← show rhoHat (χ 0) = _ from h2 0, h0]
    rw [show rhoHat (χ 1) = _ from h2 1]
    have : (((θ₁ 1 - θ₁ 0) + (θ₂ 1 - θ₂ 0) : ℝ) : ℂ) * Complex.I =
        ((θ₁ 1 : ℂ) * Complex.I - (θ₁ 0 : ℂ) * Complex.I) +
          ((θ₂ 1 : ℂ) * Complex.I - (θ₂ 0 : ℂ) * Complex.I) := by push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_sub, Complex.exp_sub, e10, e12]
    have hne : Complex.exp ((θ₂ 0 : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have hsum' : ((θ₁ 1 - θ₁ 0) + (θ₂ 1 - θ₂ 0) : ℝ) = Real.pi * k := by linarith
  rw [hsum', rhoHat_W _ hW] at hexp
  have hpow : Complex.exp ((Real.pi * k : ℝ) * Complex.I) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
    rw [show ((Real.pi * k : ℝ) : ℂ) * Complex.I = (k : ℂ) * (Real.pi * Complex.I) by
      push_cast; ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]
    push_cast; rfl
  rw [hpow] at hexp
  have hreal : (-1 : ℝ) ^ k = (-1) ^ n * Real.sign (1 - χ 1).det := by exact_mod_cast hexp
  rw [hs, zpow_sub₀ (by norm_num), hreal, zpow_natCast]
  rcases Real.sign_apply_eq (1 - χ 1).det with h | h | h <;>
    rcases neg_one_pow_eq_or ℝ n with hn | hn <;> rw [h, hn] <;> norm_num
